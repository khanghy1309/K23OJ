import json
import logging
import os
import posixpath
import re
import shutil
import threading
import tempfile
import time
import traceback
import uuid
import zipfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import timedelta
from operator import itemgetter
from random import randrange

import yaml

from django.conf import settings
from django.contrib.auth import get_user_model
from django.contrib.auth.decorators import login_required
from django.contrib.auth.mixins import LoginRequiredMixin, PermissionRequiredMixin
from django.core.cache import cache
from django.core.exceptions import ObjectDoesNotExist, PermissionDenied
from django.core.files import File
from django.db import close_old_connections, transaction
from django.db.models import BooleanField, Case, F, Max, Prefetch, Q, When
from django.db.utils import ProgrammingError
from django.http import Http404, HttpResponse, HttpResponseForbidden, HttpResponseRedirect, JsonResponse
from django.shortcuts import get_object_or_404
from django.template.loader import get_template
from django.urls import reverse
from django.utils import timezone, translation
from django.utils.functional import cached_property
from django.utils.html import escape, format_html
from django.utils.safestring import mark_safe
from django.utils.translation import gettext as _, gettext_lazy
from django.views.generic import CreateView, DetailView, FormView, ListView, UpdateView, View
from django.views.generic.base import TemplateResponseMixin
from django.views.generic.detail import SingleObjectMixin
from reversion import revisions

from judge.comments import CommentedDetailView
from judge.forms import LanguageLimitFormSet, ProblemCloneForm, ProblemEditForm, ProblemEditTypeGroupForm, \
    ProblemImportPolygonForm, ProblemImportPolygonStatementFormSet, ProblemSubmitForm, ProposeProblemSolutionFormSet, \
    ProblemAutoProblemForm, AutoProblemContestCreateFormSet, AutoProblemAddToExistingContestForm
from judge.models import Contest, ContestProblem, ContestSubmission, Judge, Language, Organization, Problem, ProblemGroup, ProblemTestCase, \
    ProblemTranslation, ProblemType, RuntimeVersion, Solution, Submission, SubmissionSource, SubmissionSourceAccess, \
    ProblemData, problem_data_storage
from judge.models.problem import ProblemTestcaseAccess
from judge.tasks import on_new_contest, on_new_problem
from judge.template_context import misc_config
from judge.utils.codeforces_polygon import ImportPolygonError, PolygonImporter
from judge.utils.diggpaginator import DiggPaginator
from judge.utils.opengraph import generate_opengraph
from judge.utils.pdfoid import PDF_RENDERING_ENABLED, render_pdf
from judge.utils.problem_data import get_visible_content
from judge.utils.problem_data import ProblemDataCompiler, get_visible_content
from judge.utils.problems import hot_problems, user_attempted_ids, \
    user_completed_ids
from judge.utils.strings import safe_float_or_none, safe_int_or_none
from judge.utils.tickets import own_ticket_filter
from judge.utils.views import QueryStringSortMixin, SingleObjectFormView, TitleMixin, add_file_response, generic_message
from judge.views.widgets import pdf_statement_uploader, submission_uploader

recjk = re.compile(r'[\u2E80-\u2E99\u2E9B-\u2EF3\u2F00-\u2FD5\u3005\u3007\u3021-\u3029\u3038-\u303A\u303B\u3400-\u4DB5'
                   r'\u4E00-\u9FC3\uF900-\uFA2D\uFA30-\uFA6A\uFA70-\uFAD9\U00020000-\U0002A6D6\U0002F800-\U0002FA1D]')


def _get_problem_archive_path(problem):
    init_path = '%s/init.yml' % problem.code
    if not problem_data_storage.exists(init_path):
        return None
    try:
        init_content = yaml.safe_load(problem_data_storage.open(init_path).read())
    except Exception:
        return None
    archive_name = init_content.get('archive') if isinstance(init_content, dict) else None
    if not archive_name:
        return None
    archive_path = '%s/%s' % (problem.code, archive_name)
    if not problem_data_storage.exists(archive_path):
        return None
    return archive_path


def get_contest_problem(problem, profile):
    try:
        return problem.contests.get(contest_id=profile.current_contest.contest_id)
    except ObjectDoesNotExist:
        return None


def get_contest_submission_count(problem, profile, virtual):
    return profile.current_contest.submissions.exclude(submission__status__in=['IE']) \
                  .filter(problem__problem=problem, participation__virtual=virtual).count()


class ProblemMixin(object):
    model = Problem
    slug_url_kwarg = 'problem'
    slug_field = 'code'

    def get_object(self, queryset=None):
        problem = super(ProblemMixin, self).get_object(queryset)
        if not problem.is_accessible_by(self.request.user):
            raise Http404()
        return problem

    def no_such_problem(self):
        code = self.kwargs.get(self.slug_url_kwarg, None)
        return generic_message(self.request, _('No such problem'),
                               _('Could not find a problem with the code "%s".') % code, status=404)

    def get(self, request, *args, **kwargs):
        try:
            return super(ProblemMixin, self).get(request, *args, **kwargs)
        except Http404:
            return self.no_such_problem()


class SolvedProblemMixin(object):
    def get_completed_problems(self):
        return user_completed_ids(self.profile) if self.profile is not None else ()

    def get_attempted_problems(self):
        return user_attempted_ids(self.profile) if self.profile is not None else ()

    @cached_property
    def in_contest(self):
        return self.profile is not None and self.profile.current_contest is not None

    @cached_property
    def contest(self):
        return self.request.profile.current_contest.contest

    @cached_property
    def profile(self):
        if not self.request.user.is_authenticated:
            return None
        return self.request.profile


class ProblemSolution(SolvedProblemMixin, ProblemMixin, TitleMixin, CommentedDetailView):
    context_object_name = 'problem'
    template_name = 'problem/editorial.html'

    def get_title(self):
        return _('Editorial for {0}').format(self.object.name)

    def get_content_title(self):
        return mark_safe(escape(_('Editorial for {0}')).format(
            format_html('<a href="{1}">{0}</a>', self.object.name, reverse('problem_detail', args=[self.object.code])),
        ))

    def get_context_data(self, **kwargs):
        context = super(ProblemSolution, self).get_context_data(**kwargs)

        solution = get_object_or_404(Solution, problem=self.object)

        if not solution.is_accessible_by(self.request.user) or self.request.in_contest:
            raise Http404()
        context['solution'] = solution
        context['has_solved_problem'] = self.object.id in self.get_completed_problems()
        return context

    def get_comment_page(self):
        return 's:' + self.object.code

    def no_such_problem(self):
        code = self.kwargs.get(self.slug_url_kwarg, None)
        return generic_message(self.request, _('No such editorial'),
                               _('Could not find an editorial with the code "%s".') % code, status=404)


class ProblemRaw(ProblemMixin, TitleMixin, TemplateResponseMixin, SingleObjectMixin, View):
    context_object_name = 'problem'
    template_name = 'problem/raw.html'

    def get_title(self):
        return self.object.name

    def get_context_data(self, **kwargs):
        context = super(ProblemRaw, self).get_context_data(**kwargs)

        try:
            trans = self.object.translations.get(language=self.request.LANGUAGE_CODE)
        except ProblemTranslation.DoesNotExist:
            trans = None

        context['problem_name'] = self.object.name if trans is None else trans.name
        context['url'] = self.request.build_absolute_uri()
        context['description'] = self.object.description if trans is None else trans.description
        return context

    def get(self, request, *args, **kwargs):
        self.object = self.get_object()
        with translation.override(settings.LANGUAGE_CODE):
            return self.render_to_response(self.get_context_data(
                object=self.object,
            ))


class ProblemDetail(ProblemMixin, SolvedProblemMixin, CommentedDetailView):
    context_object_name = 'problem'
    template_name = 'problem/problem.html'

    def get_object(self, queryset=None):
        problem = super(ProblemDetail, self).get_object(queryset)

        user = self.request.user
        authed = user.is_authenticated
        self.contest_problem = (None if not authed or user.profile.current_contest is None else
                                get_contest_problem(problem, user.profile))

        return problem

    def is_comment_locked(self):
        if self.contest_problem and self.contest_problem.contest.use_clarifications:
            return True

        return super(ProblemDetail, self).is_comment_locked()

    def get_comment_page(self):
        return 'p:%s' % self.object.code

    def get_context_data(self, **kwargs):
        context = super(ProblemDetail, self).get_context_data(**kwargs)
        user = self.request.user
        authed = user.is_authenticated
        contest_problem = self.contest_problem
        context['has_submissions'] = authed and Submission.objects.filter(user=user.profile,
                                                                          problem=self.object).exists()
        # The action dock shows the author's own last few attempts so the page answers
        # "where am I on this problem" without a round trip to the submission list.
        # Contest mode is excluded: what a participant may see there is scoped by the
        # contest's own visibility rules, which this shortcut does not evaluate.
        if authed and not self.request.in_contest:
            context['recent_submissions'] = Submission.objects.filter(
                user=user.profile, problem=self.object,
            ).order_by('-id')[:5]
        context['contest_problem'] = contest_problem
        if contest_problem:
            clarifications = self.object.clarifications
            context['has_clarifications'] = clarifications.count() > 0
            context['clarifications'] = clarifications.order_by('-date')
            context['submission_limit'] = contest_problem.max_submissions
            if contest_problem.max_submissions:
                context['submissions_left'] = max(contest_problem.max_submissions -
                                                  get_contest_submission_count(self.object, user.profile,
                                                                               user.profile.current_contest.virtual), 0)

        context['available_judges'] = Judge.objects.filter(online=True, problems=self.object)
        context['show_languages'] = self.object.allowed_languages.count() != Language.objects.count()
        context['has_pdf_render'] = PDF_RENDERING_ENABLED
        context['completed_problem_ids'] = self.get_completed_problems()
        context['attempted_problems'] = self.get_attempted_problems()
        context['has_sample_testcases'] = self.object.is_testcase_accessible_by(user) and \
            ProblemTestCase.objects.filter(dataset=self.object, is_sample=True).exists()

        can_edit = self.object.is_editable_by(user)
        context['can_edit_problem'] = can_edit
        if user.is_authenticated:
            tickets = self.object.tickets
            if not can_edit:
                tickets = tickets.filter(own_ticket_filter(user.profile.id))
            context['has_tickets'] = tickets.exists()
            context['num_open_tickets'] = tickets.filter(is_open=True).values('id').distinct().count()

        try:
            context['editorial'] = Solution.objects.get(problem=self.object)
        except ObjectDoesNotExist:
            pass
        try:
            translation = self.object.translations.get(language=self.request.LANGUAGE_CODE)
        except ProblemTranslation.DoesNotExist:
            context['title'] = self.object.name
            context['language'] = settings.LANGUAGE_CODE
            context['description'] = self.object.description
            context['translated'] = False
        else:
            context['title'] = translation.name
            context['language'] = self.request.LANGUAGE_CODE
            context['description'] = translation.description
            context['translated'] = True

        if not self.object.og_image or not self.object.summary:
            metadata = generate_opengraph('generated-meta-problem:%s:%d' % (context['language'], self.object.id),
                                          context['description'], 'problem')
        context['meta_description'] = self.object.summary or metadata[0]
        context['og_image'] = self.object.og_image or metadata[1]
        return context


class ProblemSampleTestcases(ProblemMixin, TitleMixin, DetailView):
    context_object_name = 'problem'
    template_name = 'problem/sample-testcases.html'

    def get_title(self):
        return _('Sample testcases for {0}').format(self.object.name)

    def get_content_title(self):
        return mark_safe(escape(_('Sample testcases for {0}')).format(
            format_html('<a href="{1}">{0}</a>', self.object.name, reverse('problem_detail', args=[self.object.code])),
        ))

    def get(self, request, *args, **kwargs):
        self.object = self.get_object()
        if not self.object.is_testcase_accessible_by(request.user):
            raise Http404()
        return super(ProblemSampleTestcases, self).get(request, *args, **kwargs)

    def get_context_data(self, **kwargs):
        context = super(ProblemSampleTestcases, self).get_context_data(**kwargs)
        cases = ProblemTestCase.objects.filter(dataset=self.object, is_sample=True).order_by('order')
        sample_cases = []
        archive_error = None
        archive_path = _get_problem_archive_path(self.object)

        if archive_path and cases.exists():
            try:
                with problem_data_storage.open(archive_path, 'rb') as archive_file:
                    with zipfile.ZipFile(archive_file) as archive:
                        for case in cases:
                            if not case.input_file or not case.output_file:
                                continue
                            try:
                                input_preview = get_visible_content(archive, case.input_file)
                            except KeyError:
                                input_preview = ''
                            try:
                                output_preview = get_visible_content(archive, case.output_file)
                            except KeyError:
                                output_preview = ''
                            sample_cases.append({
                                'case': case,
                                'input_preview': input_preview,
                                'output_preview': output_preview,
                            })
            except zipfile.BadZipFile:
                archive_error = _('Sample data archive is invalid.')
        elif cases.exists():
            archive_error = _('Sample data archive is not available.')

        context['sample_cases'] = sample_cases
        context['sample_archive_error'] = archive_error
        return context


def problem_sample_testcase_download(request, problem, case_id, kind):
    problem = get_object_or_404(Problem, code=problem)
    if not problem.is_testcase_accessible_by(request.user):
        raise Http404()

    case = get_object_or_404(ProblemTestCase, dataset=problem, id=case_id, is_sample=True)
    if kind not in ('in', 'out'):
        raise Http404()

    filename = case.input_file if kind == 'in' else case.output_file
    if not filename:
        raise Http404()

    archive_path = _get_problem_archive_path(problem)
    if not archive_path:
        raise Http404()

    try:
        with problem_data_storage.open(archive_path, 'rb') as archive_file:
            with zipfile.ZipFile(archive_file) as archive:
                try:
                    data = archive.read(filename)
                except KeyError:
                    raise Http404()
    except zipfile.BadZipFile:
        raise Http404()

    response = HttpResponse(data, content_type='application/octet-stream')
    response['Content-Disposition'] = 'attachment; filename=%s' % os.path.basename(filename)
    return response


class LatexError(Exception):
    pass


class ProblemPdfView(ProblemMixin, SingleObjectMixin, View):
    logger = logging.getLogger('judge.problem.pdf')
    languages = set(map(itemgetter(0), settings.LANGUAGES))

    def get(self, request, *args, **kwargs):
        if not PDF_RENDERING_ENABLED:
            raise Http404()

        language = kwargs.get('language', self.request.LANGUAGE_CODE)
        if language not in self.languages:
            raise Http404()

        problem = self.get_object()
        pdf_basename = '%s.%s.pdf' % (problem.code, language)

        def render_problem_pdf():
            self.logger.info('Rendering PDF in %s: %s', language, problem.code)

            with translation.override(language):
                try:
                    trans = problem.translations.get(language=language)
                except ProblemTranslation.DoesNotExist:
                    trans = None

                problem_name = trans.name if trans else problem.name
                return render_pdf(
                    html=get_template('problem/raw.html').render({
                        'problem': problem,
                        'problem_name': problem_name,
                        'description': trans.description if trans else problem.description,
                        'url': request.build_absolute_uri(),
                    }).replace('"//', '"https://').replace("'//", "'https://"),
                    title=problem_name,
                )

        response = HttpResponse()
        response['Content-Type'] = 'application/pdf'
        response['Content-Disposition'] = f'inline; filename={pdf_basename}'

        if settings.DMOJ_PDF_PROBLEM_CACHE:
            pdf_filename = os.path.join(settings.DMOJ_PDF_PROBLEM_CACHE, pdf_basename)
            if not os.path.exists(pdf_filename):
                with open(pdf_filename, 'wb') as f:
                    f.write(render_problem_pdf())

            if settings.DMOJ_PDF_PROBLEM_INTERNAL:
                url_path = f'{settings.DMOJ_PDF_PROBLEM_INTERNAL}/{pdf_basename}'
            else:
                url_path = None

            add_file_response(request, response, url_path, pdf_filename)
        else:
            response.content = render_problem_pdf()

        return response


class ProblemList(QueryStringSortMixin, TitleMixin, SolvedProblemMixin, ListView):
    model = Problem
    title = gettext_lazy('Problem list')
    context_object_name = 'problems'
    template_name = 'problem/list.html'
    paginate_by = 50
    sql_sort = frozenset(('points', 'ac_rate', 'user_count', 'code', 'date'))
    manual_sort = frozenset(('name', 'group', 'solved', 'type', 'editorial'))
    all_sorts = sql_sort | manual_sort
    default_desc = frozenset(('points', 'ac_rate', 'user_count'))
    # Default sort by date
    default_sort = '-date'

    def get_paginator(self, queryset, per_page, orphans=0,
                      allow_empty_first_page=True, **kwargs):
        paginator = DiggPaginator(queryset, per_page, body=6, padding=2, orphans=orphans,
                                  count=queryset.values('pk').count(),
                                  allow_empty_first_page=allow_empty_first_page, **kwargs)
        queryset = queryset.add_i18n_name(self.request.LANGUAGE_CODE)
        sort_key = self.order.lstrip('-')
        if sort_key in self.sql_sort:
            queryset = queryset.order_by(self.order, 'id')
        elif sort_key == 'name':
            queryset = queryset.order_by('i18n_name', self.order, 'name', 'id')
        elif sort_key == 'group':
            queryset = queryset.order_by(self.order + '__name', 'name', 'id')
        elif sort_key == 'editorial':
            queryset = queryset.order_by(self.order.replace('editorial', 'has_public_editorial'), 'id')
        elif sort_key == 'solved':
            if self.request.user.is_authenticated:
                profile = self.request.profile
                solved = user_completed_ids(profile)
                attempted = user_attempted_ids(profile)

                def _solved_sort_order(problem):
                    if problem.id in solved:
                        return 1
                    if problem.id in attempted:
                        return 0
                    return -1

                queryset = list(queryset)
                queryset.sort(key=_solved_sort_order, reverse=self.order.startswith('-'))
        elif sort_key == 'type':
            if self.show_types:
                queryset = list(queryset)
                queryset.sort(key=lambda problem: problem.types_list[0] if problem.types_list else '',
                              reverse=self.order.startswith('-'))
        paginator.object_list = queryset
        return paginator

    @cached_property
    def profile(self):
        if not self.request.user.is_authenticated:
            return None
        return self.request.profile

    @staticmethod
    def apply_full_text(queryset, query):
        if recjk.search(query):
            # MariaDB can't tokenize CJK properly, fallback to LIKE '%term%' for each term.
            for term in query.split():
                queryset = queryset.filter(Q(code__icontains=term) | Q(name__icontains=term) |
                                           Q(description__icontains=term))
            return queryset
        return queryset.search(query, queryset.BOOLEAN).extra(order_by=['-relevance'])

    def get_filter(self):
        _filter = Q(is_public=True) & Q(is_organization_private=False)
        if self.profile is not None:
            _filter = Problem.q_add_author_curator_tester(_filter, self.profile)
        return _filter

    def get_normal_queryset(self):
        _filter = self.get_filter()
        queryset = Problem.objects.filter(_filter).select_related('group').defer('description', 'summary')

        if self.profile is not None and self.hide_solved:
            queryset = queryset.exclude(id__in=Submission.objects
                                        .filter(user=self.profile, result='AC', case_points__gte=F('case_total'))
                                        .values_list('problem_id', flat=True))
        if self.show_types:
            queryset = queryset.prefetch_related('types')
        queryset = queryset.annotate(has_public_editorial=Case(
            When(solution__is_public=True, solution__publish_on__lte=timezone.now(), then=True),
            default=False,
            output_field=BooleanField(),
        ))
        if self.has_public_editorial:
            queryset = queryset.filter(has_public_editorial=True)
        if self.category is not None:
            queryset = queryset.filter(group__id=self.category)
        if self.selected_types:
            queryset = queryset.filter(types__in=self.selected_types)
        if 'search' in self.request.GET:
            self.search_query = query = ' '.join(self.request.GET.getlist('search')).strip()
            if query:
                if settings.ENABLE_FTS and self.full_text:
                    queryset = self.apply_full_text(queryset, query)
                else:
                    queryset = queryset.filter(
                        Q(code__icontains=query) | Q(name__icontains=query) | Q(source__icontains=query) |
                        Q(translations__name__icontains=query, translations__language=self.request.LANGUAGE_CODE))
        self.prepoint_queryset = queryset
        if self.point_start is not None:
            queryset = queryset.filter(points__gte=self.point_start)
        if self.point_end is not None:
            queryset = queryset.filter(points__lte=self.point_end)
        return queryset.distinct()

    def get_queryset(self):
        return self.get_normal_queryset()

    def get_hot_problems(self):
        return hot_problems(timedelta(days=1), settings.DMOJ_PROBLEM_HOT_PROBLEM_COUNT)

    def get_context_data(self, **kwargs):
        context = super(ProblemList, self).get_context_data(**kwargs)
        context['hide_solved'] = int(self.hide_solved)
        context['show_types'] = int(self.show_types)
        context['has_public_editorial'] = int(self.has_public_editorial)
        context['full_text'] = int(self.full_text)
        context['category'] = self.category
        context['categories'] = ProblemGroup.objects.all()
        context['selected_types'] = self.selected_types
        context['problem_types'] = ProblemType.objects.all()
        context['has_fts'] = settings.ENABLE_FTS
        context['search_query'] = self.search_query
        context['completed_problem_ids'] = self.get_completed_problems()
        context['attempted_problems'] = self.get_attempted_problems()
        context['hot_problems'] = self.get_hot_problems()
        context['point_start'], context['point_end'], context['point_values'] = self.get_noui_slider_points()
        context.update(self.get_sort_context())
        context.update(self.get_sort_paginate_context())
        return context

    def get_noui_slider_points(self):
        points = sorted(self.prepoint_queryset.values_list('points', flat=True).distinct())
        if not points:
            return 0, 0, {}
        if len(points) == 1:
            return points[0] - 1, points[0] + 1, {
                'min': points[0] - 1,
                '50%': points[0],
                'max': points[0] + 1,
            }

        start, end = points[0], points[-1]
        if self.point_start is not None:
            start = self.point_start
        if self.point_end is not None:
            end = self.point_end
        points_map = {0.0: 'min', 1.0: 'max'}
        size = len(points) - 1
        return start, end, {points_map.get(i / size, '%.2f%%' % (100 * i / size,)): j for i, j in enumerate(points)}

    def GET_with_session(self, request, key):
        if not request.GET:
            return request.session.get(key, False)
        return request.GET.get(key, None) == '1'

    def setup_problem_list(self, request):
        self.hide_solved = self.GET_with_session(request, 'hide_solved')
        self.show_types = self.GET_with_session(request, 'show_types')
        self.full_text = self.GET_with_session(request, 'full_text')
        self.has_public_editorial = self.GET_with_session(request, 'has_public_editorial')

        self.search_query = None
        self.category = None
        self.selected_types = []

        # This actually copies into the instance dictionary...
        self.all_sorts = set(self.all_sorts)
        if not self.show_types:
            self.all_sorts.discard('type')

        self.category = safe_int_or_none(request.GET.get('category'))
        if 'type' in request.GET:
            try:
                self.selected_types = list(map(int, request.GET.getlist('type')))
            except ValueError:
                pass

        self.point_start = safe_float_or_none(request.GET.get('point_start'))
        self.point_end = safe_float_or_none(request.GET.get('point_end'))

    def get(self, request, *args, **kwargs):
        self.setup_problem_list(request)

        try:
            return super(ProblemList, self).get(request, *args, **kwargs)
        except ProgrammingError as e:
            return generic_message(request, 'FTS syntax error', e.args[1], status=400)

    def post(self, request, *args, **kwargs):
        to_update = ('hide_solved', 'show_types', 'has_public_editorial', 'full_text')
        for key in to_update:
            if key in request.GET:
                val = request.GET.get(key) == '1'
                request.session[key] = val
            else:
                request.session.pop(key, None)
        return HttpResponseRedirect(request.get_full_path())


class SuggestList(ProblemList):
    title = gettext_lazy('Suggested problem list')
    template_name = 'problem/suggest-list.html'
    permission_required = 'superuser'

    def get_filter(self):
        return Q(is_public=False) & ~Q(suggester=None)

    def get(self, request, *args, **kwargs):
        if not request.user.has_perm('judge.suggest_new_problem'):
            raise Http404
        return super(SuggestList, self).get(request, *args, **kwargs)


class LanguageTemplateAjax(View):
    def get(self, request, *args, **kwargs):
        try:
            language = get_object_or_404(Language, id=int(request.GET.get('id', 0)))
        except ValueError:
            raise Http404()
        return HttpResponse(language.template, content_type='text/plain')


class RandomProblem(ProblemList):
    def get(self, request, *args, **kwargs):
        self.setup_problem_list(request)
        if self.in_contest:
            raise Http404()

        queryset = self.get_normal_queryset()
        count = queryset.count()
        if not count:
            return HttpResponseRedirect('%s%s%s' % (reverse('problem_list'), request.META['QUERY_STRING'] and '?',
                                                    request.META['QUERY_STRING']))
        return HttpResponseRedirect(queryset[randrange(count)].get_absolute_url())


user_logger = logging.getLogger('judge.user')
user_submit_ip_logger = logging.getLogger('judge.user_submit_ip_logger')
autoproblem_logger = logging.getLogger('judge.problem.autoproblem')


def get_autoproblem_temp_dir():
    """Return the disk-backed workspace used for large AutoProblem uploads."""
    temp_dir = (
        getattr(settings, 'AUTOPROBLEM_TEMP_DIR', None)
        or getattr(settings, 'FILE_UPLOAD_TEMP_DIR', None)
        or tempfile.gettempdir()
    )
    os.makedirs(temp_dir, exist_ok=True)
    return temp_dir


def process_autoproblem_upload_thread(task_id, zip_file_path, user_id, target_organization_id=None):
    timeout = 300
    copy_buffer_size = 4 * 1024 * 1024
    max_concurrency_setting = safe_int_or_none(getattr(settings, 'AUTOPROBLEM_MAX_CONCURRENCY', 10))
    max_concurrency = max(1, min(10, max_concurrency_setting or 10))
    report = {
        'created': [],
        'skipped': [],
    }

    def set_task_state(state, current=0, total=0, message='', result=None, error=None):
        payload = {
            'state': state,
            'current': current,
            'total': total,
            'message': message,
            'owner_id': user_id,
        }
        if result is not None:
            payload['result'] = result
        if error is not None:
            payload['error'] = error
        cache.set(task_id, payload, timeout=timeout)

    def build_problem_code(target_organization, sanitized_code):
        if target_organization is None:
            return sanitized_code
        prefix = ProblemAutoProblem._organization_prefix(target_organization)
        return '%s%s' % (prefix, sanitized_code)

    def get_testcase_archive_candidates(markdown_stem, sanitized_code, problem_code):
        candidates = []
        if markdown_stem:
            candidates.append('%s.zip' % markdown_stem)
        candidates.append('%s.zip' % sanitized_code)
        if problem_code != sanitized_code:
            candidates.append('%s.zip' % problem_code)
        return list(dict.fromkeys(candidates))

    def get_checker_candidates(markdown_stem, sanitized_code, problem_code):
        candidates = []
        if markdown_stem:
            candidates.append('%s_checker.cpp' % markdown_stem)
        candidates.append('%s_checker.cpp' % sanitized_code)
        if problem_code != sanitized_code:
            candidates.append('%s_checker.cpp' % problem_code)
        return list(dict.fromkeys(candidates))

    def assign_problem_ownership(problem, user, target_organization):
        if target_organization is not None:
            problem.authors.add(user.profile)
            problem.is_organization_private = True
            problem.organizations.add(target_organization)
            return
        problem.curators.add(user.profile)

    def post_problem_created(problem, target_organization):
        if target_organization is not None:
            try:
                on_new_problem.delay(problem.code)
            except Exception:
                autoproblem_logger.exception('Failed to schedule on_new_problem for %s', problem.code)

    def move_staged_file_to_storage(staged_path, storage_name):
        if not staged_path or not os.path.exists(staged_path):
            return

        # ProblemDataStorage is filesystem-backed, so moving avoids a second large file copy when possible.
        try:
            target_path = problem_data_storage.path(storage_name)
            target_dir = os.path.dirname(target_path)
            if target_dir and not os.path.isdir(target_dir):
                os.makedirs(target_dir)
            if os.path.exists(target_path):
                os.remove(target_path)
            shutil.move(staged_path, target_path)
            return
        except Exception:
            pass

        with open(staged_path, 'rb') as staged_file:
            problem_data_storage.save(storage_name, File(staged_file))
        try:
            os.remove(staged_path)
        except OSError:
            pass

    def raise_phase1_validation_error(message):
        raise ValueError(message)

    def validate_phase1_package(statement_entries, valid_member_names, target_organization):
        if not statement_entries:
            raise_phase1_validation_error(_('Error: No valid .md or .pdf statement files found. Check your ZIP structure.'))

        for statement_entry in statement_entries:
            statement_path = statement_entry.get('pdf_path') or statement_entry.get('markdown_path')
            statement_filename = posixpath.basename(statement_path) if statement_path else statement_entry.get('stem', '')
            statement_stem = statement_entry.get('stem', '')
            statement_dir = statement_entry.get('dir', '')
            folder_label = statement_dir or statement_stem or statement_filename

            sanitized_code = ProblemAutoProblem._sanitize_problem_code('%s.md' % statement_stem)
            problem_code = build_problem_code(target_organization, sanitized_code)

            missing_keys = []
            if not sanitized_code or not problem_code:
                missing_keys.append('problem_code')

            testcase_candidates = get_testcase_archive_candidates(statement_stem, sanitized_code, problem_code)
            testcase_exists = False
            for candidate_archive in testcase_candidates:
                candidate_path = posixpath.join(statement_dir, candidate_archive) if statement_dir else candidate_archive
                if candidate_path in valid_member_names:
                    testcase_exists = True
                    break

            if not testcase_exists:
                missing_keys.append('testcase_archive')

            if missing_keys:
                raise_phase1_validation_error(
                    _('Error in problem folder "%(folder)s": missing required metadata keys: %(keys)s.') % {
                        'folder': folder_label,
                        'keys': ', '.join(missing_keys),
                    }
                )

    upload_tmp_dir = os.path.dirname(zip_file_path)

    try:
        close_old_connections()
        set_task_state('PENDING', current=0, total=0, message=_('Initializing...'))
        set_task_state('PROGRESS', current=0, total=0, message=_('Extracting ZIP and parsing files...'))

        user_model = get_user_model()
        user = user_model.objects.select_related('profile').get(pk=user_id)

        target_organization = None
        if target_organization_id is not None:
            target_organization = Organization.objects.filter(pk=target_organization_id).first()

        default_group, default_type = ProblemAutoProblem._find_uncategorized_defaults()
        if default_group is None or default_type is None:
            raise ValueError(_('Problem groups/types are missing. Please create at least one group and one type first.'))

        prepared_problems = []

        with tempfile.TemporaryDirectory(
            prefix='autoproblem_stage_', dir=get_autoproblem_temp_dir(),
        ) as staging_dir:
            with zipfile.ZipFile(zip_file_path) as archive:
                member_name_map = {}
                for member in archive.namelist():
                    normalized_name = ProblemAutoProblem._normalize_archive_member_name(member)
                    if not normalized_name or member.endswith('/'):
                        continue
                    member_name_map[normalized_name] = member

                valid_member_names = set(ProblemAutoProblem._filter_valid_archive_files(list(member_name_map.keys())))
                statement_entries = ProblemAutoProblem._collect_statement_entries(valid_member_names)
                validate_phase1_package(statement_entries, valid_member_names, target_organization)

                allowed_languages = list(Language.objects.filter(include_in_problem=True))
                candidate_codes = []
                for statement_entry in statement_entries:
                    sanitized_code = ProblemAutoProblem._sanitize_problem_code('%s.md' % statement_entry['stem'])
                    problem_code = build_problem_code(target_organization, sanitized_code)
                    if problem_code:
                        candidate_codes.append(problem_code)

                existing_problem_codes = set(
                    Problem.objects.filter(code__in=candidate_codes).values_list('code', flat=True)
                )
                seen_codes = set()

                for index, statement_entry in enumerate(statement_entries, start=1):
                    markdown_path = statement_entry.get('markdown_path')
                    pdf_path = statement_entry.get('pdf_path')
                    statement_path = pdf_path or markdown_path
                    statement_filename = posixpath.basename(statement_path) if statement_path else '%s.md' % statement_entry['stem']
                    markdown_stem = statement_entry['stem']
                    sanitized_code = ProblemAutoProblem._sanitize_problem_code('%s.md' % markdown_stem)
                    problem_code = build_problem_code(target_organization, sanitized_code)
                    markdown_dir = statement_entry.get('dir', '')

                    if not problem_code:
                        reason = _('Filename produced an empty problem code after sanitization.')
                        report['skipped'].append({'file': statement_filename, 'reason': reason})
                        autoproblem_logger.warning('Skipping statement file %s: empty sanitized code', statement_filename)
                        continue

                    if problem_code in seen_codes:
                        reason = _('Duplicate sanitized code inside upload package.')
                        report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                        autoproblem_logger.warning(
                            'Skipping statement file %s: duplicate sanitized code %s inside package',
                            statement_filename,
                            problem_code,
                        )
                        continue
                    seen_codes.add(problem_code)

                    if problem_code in existing_problem_codes:
                        reason = _('Problem code already exists in database.')
                        report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                        autoproblem_logger.warning(
                            'Skipping statement file %s: code %s already exists',
                            statement_filename,
                            problem_code,
                        )
                        continue

                    checker_path = None
                    checker_filename = None
                    for candidate_checker in get_checker_candidates(markdown_stem, sanitized_code, problem_code):
                        candidate_path = posixpath.join(markdown_dir, candidate_checker) if markdown_dir else candidate_checker
                        if candidate_path in valid_member_names:
                            checker_path = candidate_path
                            checker_filename = posixpath.basename(candidate_path)
                            break

                    testcase_archive = None
                    testcase_path = None
                    testcase_candidates = get_testcase_archive_candidates(markdown_stem, sanitized_code, problem_code)
                    for candidate_archive in testcase_candidates:
                        candidate_path = posixpath.join(markdown_dir, candidate_archive) if markdown_dir else candidate_archive
                        if candidate_path in valid_member_names:
                            testcase_archive = candidate_archive
                            testcase_path = candidate_path
                            break

                    if testcase_path is None:
                        expected_archive = testcase_candidates[0]
                        reason = _('Missing testcase archive %(archive)s in the same directory.') % {
                            'archive': expected_archive,
                        }
                        report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                        autoproblem_logger.warning(
                            'Skipping statement file %s: testcase archive %s missing',
                            statement_filename,
                            expected_archive,
                        )
                        continue

                    testcase_basename = posixpath.basename(testcase_path)
                    testcase_stage_path = os.path.join(staging_dir, '%05d_%s' % (index, testcase_basename))
                    with archive.open(member_name_map[testcase_path], 'r') as testcase_stream, \
                            open(testcase_stage_path, 'wb') as testcase_stage_file:
                        shutil.copyfileobj(testcase_stream, testcase_stage_file, length=copy_buffer_size)

                    try:
                        with zipfile.ZipFile(testcase_stage_path, 'r') as testcase_zip:
                            valid_files = ProblemAutoProblem._filter_valid_archive_files(testcase_zip.namelist())
                    except zipfile.BadZipFile:
                        reason = _('Invalid testcase archive %(archive)s.') % {
                            'archive': testcase_archive,
                        }
                        report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                        autoproblem_logger.warning(
                            'Skipping statement file %s: invalid testcase archive %s',
                            statement_filename,
                            testcase_archive,
                        )
                        continue

                    testcase_pairs = ProblemAutoProblem._detect_testcase_pairs(valid_files)
                    if not testcase_pairs:
                        reason = _('Could not detect matching input/output testcase pairs in %(archive)s.') % {
                            'archive': testcase_archive,
                        }
                        report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                        autoproblem_logger.warning(
                            'Skipping statement file %s: no recognizable testcase pairs in %s',
                            statement_filename,
                            testcase_archive,
                        )
                        continue

                    checker_stage_path = None
                    checker_language = ProblemAutoProblem._detect_checker_language(checker_filename) if checker_filename else None
                    checker_storage_name = None
                    if checker_path and checker_language:
                        checker_stage_path = os.path.join(staging_dir, '%05d_%s' % (index, checker_filename))
                        with archive.open(member_name_map[checker_path], 'r') as checker_stream, \
                                open(checker_stage_path, 'wb') as checker_stage_file:
                            shutil.copyfileobj(checker_stream, checker_stage_file, length=copy_buffer_size)
                        checker_storage_name = '%s/%s' % (problem_code, checker_filename)

                    markdown_content = ''
                    if markdown_path:
                        with archive.open(member_name_map[markdown_path], 'r') as markdown_statement_file:
                            markdown_content = markdown_statement_file.read().decode('utf-8-sig', errors='replace')

                    problem_name, problem_statement = ProblemAutoProblem._parse_markdown_statement(markdown_content, problem_code)

                    pdf_stage_path = None
                    pdf_filename = None
                    if pdf_path:
                        pdf_filename = posixpath.basename(pdf_path)
                        pdf_stage_path = os.path.join(staging_dir, '%05d_%s' % (index, pdf_filename))
                        with archive.open(member_name_map[pdf_path], 'r') as pdf_stream, \
                                open(pdf_stage_path, 'wb') as pdf_stage_file:
                            shutil.copyfileobj(pdf_stream, pdf_stage_file, length=copy_buffer_size)
                        ProblemAutoProblem._validate_pdf_stage_file(pdf_stage_path, pdf_filename)

                    prepared_problems.append({
                        'file': statement_filename,
                        'code': problem_code,
                        'name': problem_name,
                        'statement': problem_statement,
                        'has_pdf_statement': bool(pdf_stage_path),
                        'pdf_stage_path': pdf_stage_path,
                        'pdf_filename': pdf_filename,
                        'testcase_pairs': testcase_pairs,
                        'testcase_valid_files': valid_files,
                        'testcase_stage_path': testcase_stage_path,
                        'testcase_storage_name': '%s/%s' % (problem_code, testcase_basename),
                        'checker_stage_path': checker_stage_path,
                        'checker_storage_name': checker_storage_name,
                        'checker_filename': checker_filename,
                        'checker_language': checker_language,
                    })

            created_problem_payloads = []
            set_task_state('PROGRESS', current=0, total=0, message=_('Saving problems to database...'))
            with transaction.atomic():
                # Preserve the package's sorted order in every date-based problem list.
                # A single timestamp makes the database fall back to insertion order, which
                # can vary between bulk inserts and makes a batch appear out of order.
                upload_started_at = timezone.now()
                Problem.objects.bulk_create([
                    Problem(
                        code=prepared_problem['code'],
                        name=prepared_problem['name'],
                        description=prepared_problem['statement'],
                        time_limit=1,
                        memory_limit=262144,
                        points=1,
                        partial=True,
                        group=default_group,
                        submission_source_visibility_mode=SubmissionSourceAccess.FOLLOW,
                        testcase_visibility_mode=ProblemTestcaseAccess.AUTHOR_ONLY,
                        date=upload_started_at + timedelta(microseconds=index),
                        is_test_ready=False,
                        autoproblem_task_id=task_id,
                        is_organization_private=(target_organization is not None),
                    )
                    for index, prepared_problem in enumerate(prepared_problems)
                ])

                created_problems_by_code = {
                    problem.code: problem
                    for problem in Problem.objects.filter(code__in=[item['code'] for item in prepared_problems])
                }

                for prepared_problem in prepared_problems:
                    problem = created_problems_by_code.get(prepared_problem['code'])
                    if problem is None:
                        continue

                    assign_problem_ownership(problem, user, target_organization)
                    problem.types.add(default_type)
                    problem.allowed_languages.set(allowed_languages)

                    problem_data = ProblemData.objects.create(problem=problem)
                    update_fields = []
                    problem_data.zipfile.name = prepared_problem['testcase_storage_name']
                    update_fields.append('zipfile')

                    if prepared_problem['checker_storage_name'] and prepared_problem['checker_language']:
                        problem_data.custom_checker.name = prepared_problem['checker_storage_name']
                        problem_data.checker = 'bridged'
                        problem_data.checker_args = json.dumps({
                            'files': prepared_problem['checker_filename'],
                            'lang': prepared_problem['checker_language'],
                            'type': 'default',
                        })
                        update_fields.extend(['custom_checker', 'checker', 'checker_args'])

                    problem_data.save(update_fields=tuple(update_fields))

                    cases = [
                        ProblemTestCase(
                            dataset=problem,
                            order=case_index,
                            type='C',
                            input_file=input_file,
                            output_file=output_file,
                            points=1,
                            is_pretest=False,
                            is_sample=False,
                        )
                        for case_index, (input_file, output_file) in enumerate(prepared_problem['testcase_pairs'], start=1)
                    ]
                    ProblemTestCase.objects.bulk_create(cases)

                    prepared_problem['problem'] = problem
                    prepared_problem['problem_data'] = problem_data
                    created_problem_payloads.append(prepared_problem)

                    report['created'].append({
                        'file': prepared_problem['file'],
                        'code': prepared_problem['code'],
                        'name': prepared_problem['name'],
                        'url': reverse('problem_detail', args=[prepared_problem['code']]),
                        'is_test_ready': False,
                    })

            total_generation = len(created_problem_payloads)
            for created_problem in created_problem_payloads:
                created_problem['problem_id'] = created_problem['problem'].id
                created_problem['problem_data_id'] = created_problem['problem_data'].id

            def run_phase3_for_problem(created_problem):
                close_old_connections()
                try:
                    problem = Problem.objects.get(pk=created_problem['problem_id'])
                    problem_data = ProblemData.objects.get(pk=created_problem['problem_data_id'])

                    if created_problem.get('pdf_stage_path'):
                        with open(created_problem['pdf_stage_path'], 'rb') as pdf_statement_file:
                            problem.pdf_url = pdf_statement_uploader(
                                File(pdf_statement_file, name=created_problem.get('pdf_filename'))
                            )
                        problem.save(update_fields=('pdf_url',))

                    move_staged_file_to_storage(
                        created_problem['testcase_stage_path'],
                        created_problem['testcase_storage_name'],
                    )

                    if created_problem['checker_storage_name'] and created_problem['checker_stage_path']:
                        move_staged_file_to_storage(
                            created_problem['checker_stage_path'],
                            created_problem['checker_storage_name'],
                        )

                    ProblemDataCompiler.generate(
                        problem,
                        problem_data,
                        problem.cases.order_by('order'),
                        created_problem['testcase_valid_files'],
                    )

                    problem.is_test_ready = True
                    problem.save(update_fields=('is_test_ready',))
                    post_problem_created(problem, target_organization)
                    return {
                        'ok': True,
                        'code': problem.code,
                    }
                except Exception as problem_error:
                    autoproblem_logger.exception(
                        'Phase 3 generation failed for %s in task %s',
                        created_problem.get('code', '?'),
                        task_id,
                    )
                    return {
                        'ok': False,
                        'file': created_problem.get('file', '-'),
                        'code': created_problem.get('code', ''),
                        'reason': str(problem_error),
                    }
                finally:
                    close_old_connections()

            completed_generation = 0
            if total_generation:
                set_task_state(
                    'PROGRESS',
                    current=0,
                    total=total_generation,
                    message=_('Generating testcases with %(workers)d workers...') % {'workers': max_concurrency},
                )

            with ThreadPoolExecutor(max_workers=max_concurrency) as executor:
                future_to_problem = {
                    executor.submit(run_phase3_for_problem, created_problem): created_problem
                    for created_problem in created_problem_payloads
                }
                for future in as_completed(future_to_problem):
                    created_problem = future_to_problem[future]
                    completed_generation += 1
                    code = created_problem.get('code', '')

                    try:
                        phase3_result = future.result()
                    except Exception as problem_error:
                        autoproblem_logger.exception(
                            'Unexpected phase 3 future failure for %s in task %s',
                            code,
                            task_id,
                        )
                        phase3_result = {
                            'ok': False,
                            'file': created_problem.get('file', '-'),
                            'code': code,
                            'reason': str(problem_error),
                        }

                    if not phase3_result.get('ok'):
                        report['skipped'].append({
                            'file': phase3_result.get('file', '-'),
                            'code': phase3_result.get('code', code),
                            'reason': phase3_result.get('reason', _('Unknown error while processing problem assets.')),
                        })

                    set_task_state(
                        'PROGRESS',
                        current=completed_generation,
                        total=total_generation,
                        message=_('Processed %(current)d/%(total)d: %(code)s') % {
                            'current': completed_generation,
                            'total': total_generation,
                            'code': code or '-',
                        },
                    )

            result_payload = {
                'report': report,
                'created_codes': [item['code'] for item in report['created']],
                'target_organization_id': target_organization.id if target_organization is not None else None,
                'available_problem_codes_csv': ','.join(item['code'] for item in report['created']),
            }
            cache.set(
                task_id,
                {
                    'state': 'SUCCESS',
                    'current': total_generation,
                    'total': total_generation,
                    'message': _('Upload completed successfully.'),
                    'owner_id': user_id,
                    'created_codes': result_payload['created_codes'],
                    'result': result_payload,
                },
                timeout=3600,
            )

    except Exception as e:
        autoproblem_logger.exception('Autoproblem thread %s failed', task_id)
        traceback.print_exc()
        cache.set(
            task_id,
            {
                'state': 'FAILURE',
                'current': 0,
                'total': 0,
                'message': str(e),
                'owner_id': user_id,
                'error': str(e),
            },
            timeout=3600,
        )
    finally:
        close_old_connections()
        if upload_tmp_dir and os.path.isdir(upload_tmp_dir):
            shutil.rmtree(upload_tmp_dir, ignore_errors=True)


@login_required
def autoproblem_task_status(request, task_id):
    task_key = str(task_id)
    task = cache.get(task_key)
    if not task:
        return JsonResponse({'state': 'PENDING', 'current': 0, 'total': 0, 'message': _('Initializing...')})

    if task.get('owner_id') != request.user.id:
        return JsonResponse({'state': 'FAILURE', 'message': _('You are not allowed to access this task.')}, status=403)

    response_payload = {key: value for key, value in task.items() if key != 'owner_id'}
    if response_payload.get('state') == 'FAILURE' and not response_payload.get('message'):
        response_payload['message'] = response_payload.get('error') or _('Upload failed.')
    if response_payload.get('state') == 'SUCCESS':
        response_payload['redirect_url'] = '%s?task_id=%s' % (reverse('problem_autoproblem'), task_key)
    return JsonResponse(response_payload)


@login_required
def autoproblem_task_details(request, task_id):
    task_key = str(task_id)
    task = cache.get(task_key)
    if task and task.get('owner_id') != request.user.id:
        return JsonResponse({'state': 'FAILURE', 'message': _('You are not allowed to access this task.')}, status=403)

    result = (task or {}).get('result') or {}
    report_items_by_code = {
        item.get('code'): item
        for item in (result.get('report') or {}).get('created', [])
        if item.get('code')
    }

    profile = request.profile
    problems = list(
        Problem.objects
            .filter(autoproblem_task_id=task_key)
            .filter(Q(authors=profile) | Q(curators=profile))
            .distinct()
            .order_by('date', 'id')
    )

    # Fallback to created_codes while task is still in memory but DB task linkage is not available.
    if not problems:
        created_codes = result.get('created_codes') or (task or {}).get('created_codes') or []
        if created_codes:
            problems_by_code = {
                problem.code: problem
                for problem in Problem.objects.filter(code__in=created_codes)
            }
            problems = [problems_by_code[code] for code in created_codes if code in problems_by_code]

    items = []
    for problem in problems:
        report_item = report_items_by_code.get(problem.code, {})
        items.append({
            'file': report_item.get('file', '-'),
            'code': problem.code,
            'name': problem.name,
            'url': reverse('problem_detail', args=[problem.code]),
            'is_test_ready': problem.is_test_ready,
        })

    state = 'PENDING'
    if task:
        state = task.get('state', 'PENDING')
    elif items:
        state = 'PROGRESS'

    ready_count = sum(1 for item in items if item['is_test_ready'])
    return JsonResponse({
        'state': state,
        'current': ready_count,
        'total': len(items),
        'problems': items,
    })


class ProblemSubmit(LoginRequiredMixin, ProblemMixin, TitleMixin, SingleObjectFormView):
    template_name = 'problem/submit.html'
    form_class = ProblemSubmitForm

    @cached_property
    def contest_problem(self):
        if self.request.profile.current_contest is None:
            return None
        return get_contest_problem(self.object, self.request.profile)

    @cached_property
    def remaining_submission_count(self):
        max_subs = self.contest_problem and self.contest_problem.max_submissions
        if max_subs is None:
            return None
        # When an IE submission is rejudged into a non-IE status, it will count towards the
        # submission limit. We max with 0 to ensure that `remaining_submission_count` returns
        # a non-negative integer, which is required for future checks in this view.
        return max(
            0,
            max_subs - get_contest_submission_count(
                self.object, self.request.profile, self.request.profile.current_contest.virtual,
            ),
        )

    @cached_property
    def default_language(self):
        # If the old submission exists, use its language, otherwise use the user's default language.
        if self.old_submission is not None:
            return self.old_submission.language
        return self.request.profile.language

    def get_content_title(self):
        return mark_safe(
            escape(_('Submit to %s')) % format_html(
                '<a href="{0}">{1}</a>',
                reverse('problem_detail', args=[self.object.code]),
                self.object.translated_name(self.request.LANGUAGE_CODE),
            ),
        )

    def get_title(self):
        return _('Submit to %s') % self.object.translated_name(self.request.LANGUAGE_CODE)

    def get_initial(self):
        initial = {'language': self.default_language}
        if self.old_submission is not None:
            initial['source'] = self.old_submission.source.source
        return initial

    def get_form_kwargs(self):
        kwargs = super().get_form_kwargs()
        kwargs['instance'] = Submission(user=self.request.profile, problem=self.object)

        if self.object.is_editable_by(self.request.user):
            kwargs['judge_choices'] = tuple(
                Judge.objects.filter(online=True, problems=self.object).values_list('name', 'name'),
            )
        else:
            kwargs['judge_choices'] = ()

        return kwargs

    def get_form(self, form_class=None):
        form = super().get_form(form_class)

        form.fields['language'].queryset = (
            self.object.usable_languages.order_by('name', 'key')
            .prefetch_related(Prefetch('runtimeversion_set', RuntimeVersion.objects.order_by('priority')))
        )

        form_data = getattr(form, 'cleaned_data', form.initial)
        if 'language' in form_data:
            form.fields['source'].widget.mode = form_data['language'].ace
        form.fields['source'].widget.theme = self.request.profile.resolved_ace_theme

        return form

    def get_success_url(self):
        return reverse('submission_status', args=(self.new_submission.id,))

    def form_valid(self, form):
        zip_sources = form.cleaned_data.get('submission_zip_sources') or []
        submission_count = len(zip_sources) or 1
        if (
            not self.request.user.has_perm('judge.spam_submission') and
            Submission.objects.filter(user=self.request.profile, rejudged_date__isnull=True)
                              .exclude(status__in=['D', 'IE', 'CE', 'AB']).count() + submission_count
                              > settings.DMOJ_SUBMISSION_LIMIT
        ):
            return HttpResponse(format_html('<h1>{0}</h1>', _('You submitted too many submissions.')), status=429)
        if not self.object.allowed_languages.filter(id=form.cleaned_data['language'].id).exists():
            raise PermissionDenied()
        if not self.request.user.is_superuser and self.object.banned_users.filter(id=self.request.profile.id).exists():
            return generic_message(self.request, _('Banned from submitting'),
                                   _('You have been declared persona non grata for this problem. '
                                     'You are permanently barred from submitting to this problem.'))
        # Must check for zero and not None. None means infinite submissions remaining.
        if self.remaining_submission_count == 0:
            return generic_message(self.request, _('Too many submissions'),
                                   _('You have exceeded the submission limit for this problem.'))
        if self.remaining_submission_count is not None and self.remaining_submission_count < submission_count:
            return generic_message(self.request, _('Too many submissions'),
                                   _('You have exceeded the submission limit for this problem.'))

        if settings.VNOJ_ENABLE_ORGANIZATION_CREDIT_LIMITATION:
            # check if the problem belongs to any organization
            organizations = []
            if self.object.is_organization_private:
                organizations = self.object.organizations.all()

            if len(organizations) == 0:
                # check if the contest belongs to any organization
                if self.contest_problem is not None:
                    contest_object = self.request.profile.current_contest.contest

                    if contest_object.is_organization_private:
                        organizations = contest_object.organizations.all()

            # check if org have credit to execute this submission
            for org in organizations:
                if not org.has_credit_left():
                    org_name = org.name
                    return generic_message(
                        self.request,
                        _('No credit'),
                        _(
                            'The organization %s has no credit left to execute this submission. '
                            'Ask the organization to buy more credit.',
                        )
                        % org_name,
                    )

        new_submissions = []
        contest_problem = self.contest_problem

        def build_submission(source_text=None, submission_file=None):
            submission = Submission(user=self.request.profile, problem=self.object,
                                    language=form.cleaned_data['language'])
            if contest_problem is not None:
                submission.contest_object = self.request.profile.current_contest.contest
                if self.request.profile.current_contest.live:
                    submission.locked_after = submission.contest_object.locked_after
                submission.save()
                ContestSubmission(
                    submission=submission,
                    problem=contest_problem,
                    participation=self.request.profile.current_contest,
                ).save()
            else:
                submission.save()

            source_url = ''
            if submission_file is not None:
                source_url = submission_uploader(
                    submission_file=submission_file,
                    problem_code=submission.problem.code,
                    user_id=submission.user.user.id,
                )

            source_value = (source_text or '') + source_url
            source = SubmissionSource(submission=submission, source=source_value)
            source.save()
            submission.source = source
            new_submissions.append(submission)

        with transaction.atomic():
            if zip_sources:
                for _, source_text in zip_sources:
                    build_submission(source_text=source_text)
            else:
                submission_file = form.files.get('submission_file', None)
                build_submission(source_text=form.cleaned_data['source'], submission_file=submission_file)

        for submission in new_submissions:
            submission.judge(force_judge=True, judge_id=form.cleaned_data['judge'])

        self.new_submission = new_submissions[-1]

        # In contest mode, we should log the ip
        if settings.VNOJ_OFFICIAL_CONTEST_MODE:
            ip = self.request.META['REMOTE_ADDR']
            # I didn't log the timestamp here because
            # the logger can handle it.
            user_submit_ip_logger.info(
                '%s,%s,%s',
                self.request.user.username,
                ip,
                self.new_submission.problem.code,
            )

        return super().form_valid(form)

    def get_context_data(self, **kwargs):
        context = super().get_context_data(**kwargs)
        context['langs'] = Language.objects.all()
        context['no_judges'] = not context['form'].fields['language'].queryset
        context['submission_limit'] = self.contest_problem and self.contest_problem.max_submissions
        context['submissions_left'] = self.remaining_submission_count
        context['ACE_URL'] = settings.ACE_URL
        context['default_lang'] = self.default_language
        return context

    def post(self, request, *args, **kwargs):
        try:
            return super().post(request, *args, **kwargs)
        except Http404:
            # Is this really necessary? This entire post() method could be removed if we don't log this.
            user_logger.info(
                'Naughty user %s wants to submit to %s without permission',
                request.user.username,
                kwargs.get(self.slug_url_kwarg),
            )
            return HttpResponseForbidden(
                format_html('<h1>{0}</h1>', _('You are not allowed to submit to this problem.')),
            )

    def dispatch(self, request, *args, **kwargs):
        submission_id = kwargs.get('submission')
        if submission_id is not None:
            self.old_submission = get_object_or_404(
                Submission.objects.select_related('source', 'language'),
                id=submission_id,
            )
            if self.old_submission.language.file_only:
                raise Http404()
            if not request.user.has_perm('judge.resubmit_other') and self.old_submission.user != request.profile:
                raise PermissionDenied()
        else:
            self.old_submission = None

        return super().dispatch(request, *args, **kwargs)


class ProblemClone(ProblemMixin, PermissionRequiredMixin, TitleMixin, SingleObjectFormView):
    title = gettext_lazy('Clone Problem')
    template_name = 'problem/clone.html'
    form_class = ProblemCloneForm
    permission_required = 'judge.clone_problem'

    def form_valid(self, form):
        problem = self.object

        languages = problem.allowed_languages.all()
        language_limits = problem.language_limits.all()
        organizations = problem.organizations.all()
        types = problem.types.all()
        old_code = problem.code

        problem.pk = None
        problem.is_public = False
        problem.ac_rate = 0
        problem.user_count = 0
        problem.code = form.cleaned_data['code']
        problem.date = timezone.now()
        with revisions.create_revision(atomic=True):
            problem.save(is_clone=True)
            problem.curators.add(self.request.profile)
            problem.allowed_languages.set(languages)
            problem.language_limits.set(language_limits)
            problem.organizations.set(organizations)
            problem.types.set(types)
            revisions.set_user(self.request.user)
            revisions.set_comment(_('Cloned problem from %s') % old_code)

        return HttpResponseRedirect(reverse('problem_edit', args=(problem.code,)))

    def dispatch(self, request, *args, **kwargs):
        self.object = self.get_object()
        if not self.object.is_editable_by(request.user):
            raise PermissionDenied()
        return super().dispatch(request, *args, **kwargs)


class ProblemCreate(PermissionRequiredMixin, TitleMixin, CreateView):
    template_name = 'problem/suggest.html'
    model = Problem
    form_class = ProblemEditForm
    permission_required = 'judge.add_problem'

    def get_form_kwargs(self):
        kwargs = super().get_form_kwargs()
        kwargs['user'] = self.request.user
        return kwargs

    def get_title(self):
        return _('Creating new problem')

    def get_content_title(self):
        return _('Creating new problem')

    def save_statement(self, form, problem):
        statement_file = form.files.get('statement_file', None)
        if statement_file is not None:
            problem.pdf_url = pdf_statement_uploader(statement_file)

    def form_valid(self, form):
        with revisions.create_revision(atomic=True):
            self.object = problem = form.save()
            problem.curators.add(self.request.user.profile)
            problem.allowed_languages.set(Language.objects.filter(include_in_problem=True))
            problem.date = timezone.now()
            self.save_statement(form, problem)
            problem.save()

            revisions.set_comment(_('Created on site'))
            revisions.set_user(self.request.user)

        return HttpResponseRedirect(self.get_success_url())

    def get_initial(self):
        initial = super(ProblemCreate, self).get_initial()
        initial = initial.copy()
        initial['description'] = misc_config(self.request)['misc_config']['description_example']
        initial['memory_limit'] = 262144  # 256 MB
        initial['partial'] = True
        try:
            initial['group'] = ProblemGroup.objects.get(name='Uncategorized').pk
        except ProblemGroup.DoesNotExist:
            initial['group'] = ProblemGroup.objects.order_by('id').first().pk
        try:
            initial['types'] = ProblemType.objects.get(name='uncategorized').pk
        except ProblemType.DoesNotExist:
            initial['types'] = ProblemType.objects.order_by('id').first().pk
        return initial


class ProblemSuggest(ProblemCreate):
    permission_required = 'judge.suggest_new_problem'

    def get_title(self):
        return _('Suggesting new problem')

    def get_content_title(self):
        return _('Suggesting new problem')

    def form_valid(self, form):
        with revisions.create_revision(atomic=True):
            self.object = problem = form.save()
            problem.suggester = self.request.user.profile
            problem.allowed_languages.set(Language.objects.filter(include_in_problem=True))
            problem.date = timezone.now()
            self.save_statement(form, problem)
            problem.save()

            revisions.set_comment(_('Created on site'))
            revisions.set_user(self.request.user)

        on_new_problem.delay(problem.code, is_suggested=True)
        return HttpResponseRedirect(self.get_success_url())


class ProblemImportPolygon(PermissionRequiredMixin, TitleMixin, FormView):
    title = gettext_lazy('Import problem from Codeforces Polygon package')
    template_name = 'problem/import-polygon.html'
    model = Problem
    form_class = ProblemImportPolygonForm
    permission_required = 'judge.import_polygon_package'

    def get_formset(self):
        return ProblemImportPolygonStatementFormSet(
            data=self.request.POST if self.request.POST else None,
            prefix='statements',
        )

    def get_context_data(self, **kwargs):
        context = super().get_context_data(**kwargs)
        context['formset'] = self.get_formset()
        context['site_languages_json'] = mark_safe(json.dumps({code: str(name) for code, name in settings.LANGUAGES}))
        return context

    def post(self, request, *args, **kwargs):
        form = self.get_form()
        formset = self.get_formset()
        if form.is_valid() and formset.is_valid():
            package = form.cleaned_data['package'].file
            code = form.cleaned_data['code']
            do_update = form.cleaned_data['do_update']
            config = {
                'ignore_zero_point_batches': form.cleaned_data['ignore_zero_point_batches'],
                'ignore_zero_point_cases': form.cleaned_data['ignore_zero_point_cases'],
                'append_main_solution_to_tutorial': form.cleaned_data['append_main_solution_to_tutorial'],
                'main_tutorial_language': form.cleaned_data.get('main_tutorial_language', None),
                'main_statement_language': None,
                'polygon_to_site_language_map': {},
            }
            if len(formset) > 1:
                for statement in formset:
                    polygon_language = statement.cleaned_data['polygon_language']
                    site_language = statement.cleaned_data['site_language']

                    if site_language == settings.LANGUAGE_CODE:
                        config['main_statement_language'] = polygon_language
                    else:
                        config['polygon_to_site_language_map'][polygon_language] = site_language

            try:
                importer = PolygonImporter(
                    package=package,
                    code=code,
                    authors=[self.request.profile],
                    curators=[],
                    do_update=do_update,
                    interactive=False,
                    config=config,
                )
                importer.run()
            except ImportPolygonError as e:
                return generic_message(request, _('Failed to import problem'), str(e), status=400)

            return HttpResponseRedirect(reverse('problem_detail', args=[code]))

        return self.render_to_response(self.get_context_data())


class ProblemAutoProblem(PermissionRequiredMixin, TitleMixin, FormView):
    title = gettext_lazy('Bulk upload problems from package')
    template_name = 'problem/autoproblem.html'
    form_class = ProblemAutoProblemForm
    permission_required = 'judge.add_problem'

    def has_permission(self):
        user = self.request.user
        if user.has_perm('judge.add_problem'):
            return True

        if not user.has_perm('judge.create_organization_problem'):
            return False

        profile = user.profile
        return any(org.is_admin(profile) for org in profile.organizations.all())

    @staticmethod
    def _safe_extract_archive(archive, target_dir):
        target_dir = os.path.abspath(target_dir)
        for member in archive.namelist():
            member_path = os.path.abspath(os.path.join(target_dir, member))
            if os.path.commonpath((target_dir, member_path)) != target_dir:
                raise ValueError('Archive contains unsafe paths')
        archive.extractall(target_dir)

    @staticmethod
    def _sanitize_problem_code(filename):
        raw_code = os.path.splitext(os.path.basename(filename))[0]
        sanitized = re.sub(r'[^A-Za-z0-9_]', '_', raw_code)
        sanitized = re.sub(r'_+', '_', sanitized).strip('_').lower()
        return sanitized

    @staticmethod
    def _parse_markdown_statement(markdown_content, problem_code):
        if not markdown_content:
            return problem_code, ''

        lines = markdown_content.splitlines()
        if not lines:
            return problem_code, ''

        first_line = lines[0].strip()
        if first_line.startswith('# '):
            problem_name = first_line[2:].strip() or problem_code
            statement = '\n'.join(lines[1:])
            return problem_name, statement

        return problem_code, markdown_content

    @classmethod
    def _collect_statement_entries(cls, valid_member_names):
        entries = {}
        for member_name in sorted(valid_member_names, key=cls._natural_sort_key):
            lowered_name = member_name.lower()
            if not (lowered_name.endswith('.md') or lowered_name.endswith('.pdf')):
                continue

            member_dir = posixpath.dirname(member_name)
            member_filename = posixpath.basename(member_name)
            member_stem, member_ext = posixpath.splitext(member_filename)
            statement_key = (member_dir, member_stem.lower())

            if statement_key not in entries:
                entries[statement_key] = {
                    'dir': member_dir,
                    'stem': member_stem,
                    'markdown_path': None,
                    'pdf_path': None,
                }

            if member_ext.lower() == '.md' and entries[statement_key]['markdown_path'] is None:
                entries[statement_key]['markdown_path'] = member_name
            if member_ext.lower() == '.pdf' and entries[statement_key]['pdf_path'] is None:
                entries[statement_key]['pdf_path'] = member_name

        return sorted(
            entries.values(),
            key=lambda item: cls._natural_sort_key(cls._join_archive_path(item['dir'], item['stem'])),
        )

    @staticmethod
    def _validate_pdf_stage_file(staged_path, filename):
        file_size = os.path.getsize(staged_path)
        if file_size > settings.PDF_STATEMENT_MAX_FILE_SIZE:
            raise ValueError(_('PDF statement %(filename)s exceeds the maximum allowed size.') % {
                'filename': filename,
            })

        with open(staged_path, 'rb') as pdf_file:
            header = pdf_file.read(5)
            if header != b'%PDF-':
                raise ValueError(_('Invalid PDF statement file %(filename)s.') % {'filename': filename})

            if file_size > 0:
                tail_window = min(file_size, 2048)
                pdf_file.seek(-tail_window, os.SEEK_END)
                tail = pdf_file.read(tail_window)
                if b'%%EOF' not in tail:
                    raise ValueError(_('Invalid PDF statement file %(filename)s.') % {'filename': filename})

    @staticmethod
    def _natural_sort_key(path):
        parts = re.split(r'(\d+)', path.lower())
        return [int(part) if part.isdigit() else part for part in parts]

    @staticmethod
    def _normalize_archive_member_name(member_name):
        normalized = member_name.replace('\\', '/')
        normalized = posixpath.normpath(normalized)
        if normalized in ('', '.'):
            return None
        if normalized.startswith('../') or normalized == '..' or normalized.startswith('/'):
            raise ValueError('Archive contains unsafe paths')
        return normalized

    @staticmethod
    def _join_archive_path(parent, child):
        if not parent:
            return child
        return posixpath.join(parent, child)

    @staticmethod
    def _filter_valid_archive_files(file_list):
        return [
            file_name for file_name in file_list
            if not file_name.startswith('__MACOSX/') and
            not file_name.startswith('._') and
            '/._' not in file_name and
            not file_name.endswith('/.DS_Store') and
            file_name != '.DS_Store'
        ]

    @classmethod
    def _detect_testcase_pairs(cls, valid_files):
        in_files = []
        out_files = []
        detected_format = -1

        in_patterns = [
            re.compile(r'^(.+\.inp|.+\.in|inp|in)$'),
            re.compile(r'^input\.(.+\d+)$'),
            re.compile(r'^(.+\d+)$'),
        ]
        out_patterns = [
            re.compile(r'^(.+\.out|.+\.ok|.+\.ans|.+\.sol|out|ok|ans|sol)$'),
            re.compile(r'^output\.(.+\d+)$'),
            re.compile(r'^(.+\d+\.a)$'),
        ]

        for file_name in valid_files:
            tested_name = os.path.basename(file_name).lower()
            for idx in range(3):
                if in_patterns[idx].match(tested_name):
                    if detected_format not in (-1, idx):
                        return []
                    detected_format = idx
                    in_files.append(file_name)
                    break
                if out_patterns[idx].match(tested_name):
                    if detected_format not in (-1, idx):
                        return []
                    detected_format = idx
                    out_files.append(file_name)
                    break

        if not in_files or len(in_files) != len(out_files):
            return []

        in_files.sort(key=cls._natural_sort_key)
        out_files.sort(key=cls._natural_sort_key)
        return list(zip(in_files, out_files))

    def build_problem_code(self, sanitized_code):
        if self.target_organization is not None:
            prefix = ''.join(x for x in self.target_organization.slug.lower() if x.isalnum()) + '_'
            return prefix + sanitized_code
        return sanitized_code

    def get_testcase_archive_candidates(self, markdown_stem, sanitized_code, problem_code):
        candidates = []
        if markdown_stem:
            candidates.append('%s.zip' % markdown_stem)
        candidates.append('%s.zip' % sanitized_code)
        if problem_code != sanitized_code:
            candidates.append('%s.zip' % problem_code)
        return list(dict.fromkeys(candidates))

    def get_checker_candidates(self, markdown_stem, sanitized_code, problem_code):
        candidates = []
        if markdown_stem:
            candidates.append('%s_checker.cpp' % markdown_stem)
        candidates.append('%s_checker.cpp' % sanitized_code)
        if problem_code != sanitized_code:
            candidates.append('%s_checker.cpp' % problem_code)
        return list(dict.fromkeys(candidates))

    @staticmethod
    def _detect_checker_language(checker_filename):
        extension = os.path.splitext(checker_filename)[1].lower()
        if extension == '.cpp':
            return 'CPP17'
        if extension == '.pas':
            return 'PAS'
        if extension == '.java':
            return 'JAVA8'
        return None

    def assign_problem_ownership(self, problem):
        if self.target_organization is not None:
            problem.authors.add(self.request.user.profile)
            problem.is_organization_private = True
            problem.organizations.add(self.target_organization)
            return
        problem.curators.add(self.request.profile)

    def post_problem_created(self, problem):
        if self.target_organization is not None:
            try:
                on_new_problem.delay(problem.code)
            except Exception:
                autoproblem_logger.exception('Failed to schedule on_new_problem for %s', problem.code)
        return None

    @staticmethod
    def _find_uncategorized_defaults():
        group = ProblemGroup.objects.filter(name__iexact='Uncategorized').first()
        if group is None:
            group = ProblemGroup.objects.order_by('id').first()

        type_ = ProblemType.objects.filter(name__iexact='uncategorized').first()
        if type_ is None:
            type_ = ProblemType.objects.order_by('id').first()

        return group, type_

    def get_context_data(self, **kwargs):
        context = super().get_context_data(**kwargs)
        context.setdefault('report', None)
        return context

    def get_form_kwargs(self):
        kwargs = super().get_form_kwargs()
        kwargs['user'] = self.request.user
        return kwargs

    @staticmethod
    def _organization_prefix(organization):
        if organization is None:
            return ''
        return ''.join(x for x in organization.slug.lower() if x.isalnum()) + '_'

    @staticmethod
    def _build_contest_problem_choices(created_items):
        return [
            (item['code'], '%s - %s' % (item['code'], item['name']))
            for item in created_items
        ]

    def _can_create_organization_contest(self, organization):
        user = self.request.user
        if organization is None:
            return False
        if not user.has_perm('judge.create_private_contest'):
            return False
        return organization.is_admin(user.profile)

    def _can_create_regular_contest(self):
        return self.request.user.has_perm('judge.add_contest')

    def _can_create_any_organization_contest(self):
        user = self.request.user
        if not user.has_perm('judge.create_private_contest'):
            return False
        profile = user.profile
        return any(org.is_admin(profile) for org in profile.organizations.all())

    def _get_contest_formset(self, created_items, target_organization=None, data=None):
        kwargs = {
            'prefix': 'contests',
            'form_kwargs': {
                'user': self.request.user,
                'problem_choices': self._build_contest_problem_choices(created_items),
                'target_organization': target_organization,
            },
        }
        if data is not None:
            kwargs['data'] = data
        return AutoProblemContestCreateFormSet(**kwargs)

    def _get_unbound_upload_form(self):
        """Build the upload form without data from a contest-management POST."""
        return self.get_form_class()(user=self.request.user)

    def _get_add_existing_contest_form(self, created_items, data=None):
        kwargs = {
            'user': self.request.user,
            'problem_choices': self._build_contest_problem_choices(created_items),
        }
        if data is not None:
            return AutoProblemAddToExistingContestForm(data=data, **kwargs)
        return AutoProblemAddToExistingContestForm(**kwargs)

    def _can_edit_contest_for_autoproblem(self, contest):
        user = self.request.user
        if user.has_perm('judge.change_contest') or user.has_perm('judge.edit_all_contest'):
            return True
        if contest.is_editable_by(user):
            return True
        if contest.is_organization_private and contest.organizations.filter(admins=user.profile).exists():
            return True
        return False

    def _build_contest_org_prefix_map(self, contest_formset):
        if contest_formset is None or not contest_formset.forms:
            return {}
        contest_form = contest_formset.forms[0]
        return {
            str(org.id): self._organization_prefix(org)
            for org in contest_form.fields['organization'].queryset
        }

    def _build_report_created_from_codes(self, problem_codes):
        problems_by_code = {
            problem.code: problem
            for problem in Problem.objects.filter(code__in=problem_codes)
        }

        created_items = []
        for code in problem_codes:
            problem = problems_by_code.get(code)
            if problem is None:
                continue
            created_items.append({
                'file': '-',
                'code': problem.code,
                'name': problem.name,
                'url': reverse('problem_detail', args=[problem.code]),
                'is_test_ready': problem.is_test_ready,
            })
        return created_items

    @staticmethod
    def _parse_created_contest_keys(raw_keys):
        if not raw_keys:
            return []
        return [key.strip() for key in raw_keys.split(',') if key.strip()]

    @staticmethod
    def _serialize_created_contest_keys(keys):
        return ','.join(keys)

    @staticmethod
    def _build_created_contests(created_contest_keys):
        contests_by_key = {
            contest.key: contest
            for contest in Contest.objects.filter(key__in=created_contest_keys)
        }
        created_contests = []
        for key in created_contest_keys:
            contest = contests_by_key.get(key)
            if contest is None:
                continue
            created_contests.append({
                'key': contest.key,
                'name': contest.name,
                'url': reverse('contest_view', args=[contest.key]),
            })
        return created_contests

    def _create_contest_from_autoproblem(self, contest_form):
        is_organization = contest_form.cleaned_data['is_organization']
        organization = contest_form.cleaned_data.get('organization')
        selected_codes = contest_form.cleaned_data['selected_problems']

        if is_organization:
            if not self._can_create_organization_contest(organization):
                contest_form.add_error('is_organization', _('You do not have permission to create organization contests.'))
                return None
        elif not self._can_create_regular_contest():
            contest_form.add_error('is_organization', _('You do not have permission to create regular contests.'))
            return None

        selected_problems = list(Problem.objects.filter(code__in=selected_codes))
        selected_problem_codes = {problem.code for problem in selected_problems}
        if len(selected_problem_codes) != len(set(selected_codes)):
            contest_form.add_error('selected_problems', _('One or more selected problems were not found.'))
            return None

        for problem in selected_problems:
            if not problem.is_editable_by(self.request.user):
                contest_form.add_error('selected_problems', _('One or more selected problems are not editable by you.'))
                return None

        order_map = {code: index for index, code in enumerate(selected_codes, start=1)}
        now = timezone.now()

        with transaction.atomic():
            with revisions.create_revision(atomic=False):
                contest = Contest.objects.create(
                    key=contest_form.cleaned_data['contest_id'],
                    name=contest_form.cleaned_data['contest_name'],
                    start_time=now,
                    end_time=now + timedelta(minutes=10),
                    is_visible=False,
                    use_clarifications=True,
                    hide_problem_tags=False,
                    hide_problem_authors=False,
                    show_short_display=False,
                    scoreboard_visibility=Contest.SCOREBOARD_VISIBLE,
                    format_name='default',
                )
                contest.authors.add(self.request.profile)

                if is_organization:
                    contest.is_organization_private = True
                    contest.save(update_fields=('is_organization_private',))
                    contest.organizations.add(organization)

                contest_problems = [
                    ContestProblem(
                        contest=contest,
                        problem=problem,
                        points=1,
                        order=order_map[problem.code],
                        partial=True,
                    )
                    for problem in selected_problems
                ]
                ContestProblem.objects.bulk_create(contest_problems)

                revisions.set_comment(_('Created contest from /autoproblem upload'))
                revisions.set_user(self.request.user)

        try:
            on_new_contest.delay(contest.key)
        except Exception:
            autoproblem_logger.exception('Failed to schedule on_new_contest for %s', contest.key)
        return contest

    def _handle_contest_create_post(self, request, *args, **kwargs):
        available_codes_raw = request.POST.get('available_problem_codes', '')
        available_codes = [code.strip() for code in available_codes_raw.split(',') if code.strip()]
        created_items = self._build_report_created_from_codes(available_codes)
        available_problem_codes_csv = ','.join(item['code'] for item in created_items)
        created_contest_keys = self._parse_created_contest_keys(request.POST.get('created_contest_keys', ''))

        contest_formset = self._get_contest_formset(created_items, data=request.POST)
        add_existing_form = self._get_add_existing_contest_form(created_items)
        contests_created_in_submit = 0
        contest_create_error = None

        if contest_formset.is_valid():
            for contest_form in contest_formset.forms:
                if contest_form.cleaned_data.get('DELETE'):
                    continue
                if not contest_form.has_changed():
                    continue
                contest = self._create_contest_from_autoproblem(contest_form)
                if contest is None:
                    contest_create_error = _('Some contest forms contain invalid data. Please review and submit again.')
                    break
                contests_created_in_submit += 1
                if contest.key not in created_contest_keys:
                    created_contest_keys.append(contest.key)

            if contests_created_in_submit > 0 and contest_create_error is None:
                contest_formset = self._get_contest_formset(created_items)
            elif contests_created_in_submit == 0 and contest_create_error is None:
                contest_create_error = _('Please fill at least one contest form before creating contests.')

        contest_org_prefix_map_json = json.dumps(self._build_contest_org_prefix_map(contest_formset))

        report = {
            'created': created_items,
            'skipped': [],
        }
        return self.render_to_response(self.get_context_data(
            form=self._get_unbound_upload_form(),
            report=report,
            contest_formset=contest_formset,
            add_existing_contest_form=add_existing_form,
            contest_org_prefix_map_json=contest_org_prefix_map_json,
            contest_created_success=contests_created_in_submit > 0,
            contests_created_in_submit=contests_created_in_submit,
            contest_create_error=contest_create_error,
            add_existing_success=False,
            add_existing_added_count=0,
            add_existing_skipped_count=0,
            add_existing_error=None,
            add_existing_contest=None,
            created_contests=self._build_created_contests(created_contest_keys),
            created_contest_keys=self._serialize_created_contest_keys(created_contest_keys),
            available_problem_codes_csv=available_problem_codes_csv,
            contest_action_mode='create_new',
        ))

    def _handle_add_to_existing_contest_post(self, request, *args, **kwargs):
        available_codes_raw = request.POST.get('available_problem_codes', '')
        available_codes = [code.strip() for code in available_codes_raw.split(',') if code.strip()]
        created_items = self._build_report_created_from_codes(available_codes)
        available_problem_codes_csv = ','.join(item['code'] for item in created_items)
        created_contest_keys = self._parse_created_contest_keys(request.POST.get('created_contest_keys', ''))

        can_create_contest = self._can_create_regular_contest() or self._can_create_any_organization_contest()
        contest_formset = self._get_contest_formset(created_items) if can_create_contest else None
        add_existing_form = self._get_add_existing_contest_form(created_items, data=request.POST)
        add_existing_success = False
        add_existing_added_count = 0
        add_existing_skipped_count = 0
        add_existing_error = None
        add_existing_contest = None

        if add_existing_form.is_valid():
            contest = add_existing_form.cleaned_data['existing_contest']
            if not self._can_edit_contest_for_autoproblem(contest):
                add_existing_form.add_error('existing_contest', _('You do not have permission to edit this contest.'))
                add_existing_error = _('Invalid contest selection.')
            else:
                selected_codes = add_existing_form.cleaned_data['selected_problems']
                selected_problems = list(Problem.objects.filter(code__in=selected_codes))
                selected_problems_by_code = {problem.code: problem for problem in selected_problems}
                if len(selected_problems_by_code) != len(set(selected_codes)):
                    add_existing_form.add_error('selected_problems', _('One or more selected problems were not found.'))
                    add_existing_error = _('Some selected problems are invalid.')
                else:
                    for problem in selected_problems:
                        if not problem.is_editable_by(self.request.user):
                            add_existing_form.add_error(
                                'selected_problems',
                                _('One or more selected problems are not editable by you.'),
                            )
                            add_existing_error = _('Some selected problems are not editable by you.')
                            break

                if add_existing_error is None:
                    existing_problem_ids = set(
                        ContestProblem.objects.filter(contest=contest).values_list('problem_id', flat=True)
                    )
                    max_order = ContestProblem.objects.filter(contest=contest).aggregate(Max('order'))['order__max'] or 0
                    next_order = max_order
                    contest_problems_to_create = []

                    for code in selected_codes:
                        problem = selected_problems_by_code.get(code)
                        if problem is None:
                            continue
                        if problem.id in existing_problem_ids:
                            add_existing_skipped_count += 1
                            continue

                        next_order += 1
                        contest_problems_to_create.append(ContestProblem(
                            contest=contest,
                            problem=problem,
                            points=1,
                            order=next_order,
                            partial=True,
                        ))
                        existing_problem_ids.add(problem.id)

                    if contest_problems_to_create:
                        ContestProblem.objects.bulk_create(contest_problems_to_create)
                        add_existing_added_count = len(contest_problems_to_create)
                        add_existing_success = True
                        add_existing_contest = {
                            'key': contest.key,
                            'name': contest.name,
                            'url': reverse('contest_view', args=[contest.key]),
                        }
                        add_existing_form = self._get_add_existing_contest_form(created_items)
                    elif add_existing_skipped_count > 0:
                        add_existing_error = _('All selected problems are already in the chosen contest.')
                    else:
                        add_existing_error = _('Please select at least one problem to add.')

        report = {
            'created': created_items,
            'skipped': [],
        }
        contest_org_prefix_map_json = json.dumps(self._build_contest_org_prefix_map(contest_formset))
        return self.render_to_response(self.get_context_data(
            form=self._get_unbound_upload_form(),
            report=report,
            contest_formset=contest_formset,
            add_existing_contest_form=add_existing_form,
            contest_org_prefix_map_json=contest_org_prefix_map_json,
            contest_created_success=False,
            contests_created_in_submit=0,
            contest_create_error=None,
            add_existing_success=add_existing_success,
            add_existing_added_count=add_existing_added_count,
            add_existing_skipped_count=add_existing_skipped_count,
            add_existing_error=add_existing_error,
            add_existing_contest=add_existing_contest,
            created_contests=self._build_created_contests(created_contest_keys),
            created_contest_keys=self._serialize_created_contest_keys(created_contest_keys),
            available_problem_codes_csv=available_problem_codes_csv,
            contest_action_mode='add_existing',
        ))

    def get(self, request, *args, **kwargs):
        task_id = request.GET.get('task_id')
        force_check = request.GET.get('force_check') == '1'
        if task_id or force_check:
            task_data = cache.get(task_id) if task_id else None
            result = {}
            report = {'created': [], 'skipped': []}
            created_codes = []
            target_organization_id = None

            if task_data and task_data.get('owner_id') == request.user.id:
                result = task_data.get('result') or {}
                report = result.get('report') or report
                created_codes.extend(result.get('created_codes') or task_data.get('created_codes') or [])
                target_organization_id = result.get('target_organization_id')

            if task_id:
                task_db_codes = list(
                    Problem.objects
                        .filter(autoproblem_task_id=task_id)
                        .filter(Q(authors=request.profile) | Q(curators=request.profile))
                        .order_by('date', 'id')
                        .values_list('code', flat=True)
                )
                created_codes.extend(task_db_codes)

            # Rescue/discovery mode for stalled cache state: include recent authored/curated problems.
            if force_check or not created_codes:
                recent_threshold = timezone.now() - timedelta(minutes=30)
                recent_codes = list(
                    Problem.objects
                        .filter(date__gte=recent_threshold)
                        .filter(Q(authors=request.profile) | Q(curators=request.profile))
                        .order_by('-date')
                        .values_list('code', flat=True)
                )
                created_codes.extend(recent_codes)

            merged_codes = list(dict.fromkeys(code for code in created_codes if code))
            if merged_codes:
                problems_by_code = {
                    problem.code: problem
                    for problem in Problem.objects.filter(code__in=merged_codes)
                }
                report_items_by_code = {
                    item.get('code'): item
                    for item in report.get('created', [])
                    if item.get('code')
                }
                created_items = []
                for code in merged_codes:
                    problem = problems_by_code.get(code)
                    if problem is None:
                        continue
                    report_item = report_items_by_code.get(code, {})
                    created_items.append({
                        'file': report_item.get('file', '-'),
                        'code': problem.code,
                        'name': problem.name,
                        'url': reverse('problem_detail', args=[problem.code]),
                        'is_test_ready': problem.is_test_ready,
                    })
                report['created'] = created_items

                available_problem_codes_csv = result.get('available_problem_codes_csv') or \
                    ','.join(item['code'] for item in created_items)

                target_organization = None
                if target_organization_id:
                    target_organization = Organization.objects.filter(pk=target_organization_id).first()

                contest_formset = None
                add_existing_contest_form = None
                can_create_contest = self._can_create_regular_contest() or self._can_create_any_organization_contest()
                if created_items and can_create_contest:
                    contest_formset = self._get_contest_formset(created_items, target_organization=target_organization)
                if created_items:
                    add_existing_contest_form = self._get_add_existing_contest_form(created_items)

                contest_org_prefix_map_json = json.dumps(self._build_contest_org_prefix_map(contest_formset))
                return self.render_to_response(self.get_context_data(
                    form=self.get_form(),
                    report=report,
                    current_task_id=task_id or '',
                    contest_formset=contest_formset,
                    add_existing_contest_form=add_existing_contest_form,
                    contest_org_prefix_map_json=contest_org_prefix_map_json,
                    contest_created_success=False,
                    contests_created_in_submit=0,
                    contest_create_error=None,
                    add_existing_success=False,
                    add_existing_added_count=0,
                    add_existing_skipped_count=0,
                    add_existing_error=None,
                    add_existing_contest=None,
                    created_contests=[],
                    created_contest_keys='',
                    available_problem_codes_csv=available_problem_codes_csv,
                    contest_action_mode='create_new',
                ))

        return super().get(request, *args, **kwargs)

    def post(self, request, *args, **kwargs):
        if request.POST.get('form_action') == 'create_contest':
            return self._handle_contest_create_post(request, *args, **kwargs)
        if request.POST.get('form_action') == 'add_to_existing_contest':
            return self._handle_add_to_existing_contest_post(request, *args, **kwargs)

        is_ajax_request = request.headers.get('X-Requested-With') == 'XMLHttpRequest'
        if request.POST.get('form_action') == 'upload' and is_ajax_request:
            form = self.get_form()
            if not form.is_valid():
                return JsonResponse({'errors': form.errors.get_json_data()}, status=400)

            target_organization = form.cleaned_data.get('organization') if form.cleaned_data.get('is_organization') else None
            package = form.cleaned_data['package']

            upload_dir = tempfile.mkdtemp(prefix='autoproblem_upload_', dir=get_autoproblem_temp_dir())
            zip_file_path = os.path.join(upload_dir, '%s.zip' % uuid.uuid4())
            try:
                # Files above FILE_UPLOAD_MAX_MEMORY_SIZE are already in a
                # TemporaryUploadedFile. Moving it avoids making a second
                # multi-gigabyte copy before the background worker starts.
                shutil.move(package.temporary_file_path(), zip_file_path)
            except AttributeError:
                with open(zip_file_path, 'wb') as destination:
                    for chunk in package.chunks():
                        destination.write(chunk)

            task_id = str(uuid.uuid4())
            cache.set(
                task_id,
                {
                    'state': 'PENDING',
                    'current': 0,
                    'total': 0,
                    'message': _('Upload queued.'),
                    'owner_id': request.user.id,
                },
                timeout=300,
            )

            worker = threading.Thread(
                target=process_autoproblem_upload_thread,
                args=(
                    task_id,
                    zip_file_path,
                    request.user.id,
                    target_organization.id if target_organization is not None else None,
                ),
                daemon=True,
            )
            worker.start()

            return JsonResponse({'task_id': task_id})

        return super().post(request, *args, **kwargs)

    def form_valid(self, form):
        self.target_organization = form.cleaned_data.get('organization') if form.cleaned_data.get('is_organization') else None
        package = form.cleaned_data['package']
        copy_buffer_size = 4 * 1024 * 1024
        report = {
            'created': [],
            'skipped': [],
        }

        default_group, default_type = self._find_uncategorized_defaults()
        if default_group is None or default_type is None:
            return generic_message(
                self.request,
                _('Cannot create problem'),
                _('Problem groups/types are missing. Please create at least one group and one type first.'),
                status=400,
            )

        try:
            package.file.seek(0)
            prepared_problems = []

            with tempfile.TemporaryDirectory(
                prefix='autoproblem_stage_', dir=get_autoproblem_temp_dir(),
            ) as staging_dir:
                with zipfile.ZipFile(package.file) as archive:
                    member_name_map = {}
                    for member in archive.namelist():
                        normalized_name = self._normalize_archive_member_name(member)
                        if not normalized_name or member.endswith('/'):
                            continue
                        member_name_map[normalized_name] = member

                    valid_member_names = set(self._filter_valid_archive_files(list(member_name_map.keys())))
                    statement_entries = self._collect_statement_entries(valid_member_names)

                    if not statement_entries:
                        raise ValueError(_('Error: No valid .md or .pdf statement files found. Check your ZIP structure.'))

                    allowed_languages = list(Language.objects.filter(include_in_problem=True))
                    candidate_codes = []
                    for statement_entry in statement_entries:
                        sanitized_code = self._sanitize_problem_code('%s.md' % statement_entry['stem'])
                        problem_code = self.build_problem_code(sanitized_code)
                        if problem_code:
                            candidate_codes.append(problem_code)

                    existing_problem_codes = set(
                        Problem.objects.filter(code__in=candidate_codes).values_list('code', flat=True)
                    )
                    seen_codes = set()

                    for index, statement_entry in enumerate(statement_entries, start=1):
                        markdown_path = statement_entry.get('markdown_path')
                        pdf_path = statement_entry.get('pdf_path')
                        statement_path = pdf_path or markdown_path
                        statement_filename = posixpath.basename(statement_path) if statement_path else '%s.md' % statement_entry['stem']
                        markdown_stem = statement_entry['stem']
                        sanitized_code = self._sanitize_problem_code('%s.md' % markdown_stem)
                        problem_code = self.build_problem_code(sanitized_code)
                        markdown_dir = statement_entry.get('dir', '')

                        if not problem_code:
                            reason = _('Filename produced an empty problem code after sanitization.')
                            report['skipped'].append({'file': statement_filename, 'reason': reason})
                            autoproblem_logger.warning('Skipping statement file %s: empty sanitized code', statement_filename)
                            continue

                        if problem_code in seen_codes:
                            reason = _('Duplicate sanitized code inside upload package.')
                            report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                            autoproblem_logger.warning(
                                'Skipping statement file %s: duplicate sanitized code %s inside package',
                                statement_filename,
                                problem_code,
                            )
                            continue
                        seen_codes.add(problem_code)

                        if problem_code in existing_problem_codes:
                            reason = _('Problem code already exists in database.')
                            report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                            autoproblem_logger.warning(
                                'Skipping statement file %s: code %s already exists',
                                statement_filename,
                                problem_code,
                            )
                            continue

                        checker_path = None
                        checker_filename = None
                        for candidate_checker in self.get_checker_candidates(markdown_stem, sanitized_code, problem_code):
                            candidate_path = self._join_archive_path(markdown_dir, candidate_checker)
                            if candidate_path in valid_member_names:
                                checker_path = candidate_path
                                checker_filename = posixpath.basename(candidate_path)
                                break

                        testcase_archive = None
                        testcase_path = None
                        testcase_candidates = self.get_testcase_archive_candidates(markdown_stem, sanitized_code, problem_code)
                        for candidate_archive in testcase_candidates:
                            candidate_path = self._join_archive_path(markdown_dir, candidate_archive)
                            if candidate_path in valid_member_names:
                                testcase_archive = candidate_archive
                                testcase_path = candidate_path
                                break

                        if testcase_path is None:
                            expected_archive = testcase_candidates[0]
                            reason = _('Missing testcase archive %(archive)s in the same directory.') % {
                                'archive': expected_archive,
                            }
                            report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                            autoproblem_logger.warning(
                                'Skipping statement file %s: testcase archive %s missing',
                                statement_filename,
                                expected_archive,
                            )
                            continue

                        testcase_basename = posixpath.basename(testcase_path)
                        testcase_stage_path = os.path.join(staging_dir, '%05d_%s' % (index, testcase_basename))
                        with archive.open(member_name_map[testcase_path], 'r') as testcase_stream, \
                                open(testcase_stage_path, 'wb') as testcase_stage_file:
                            shutil.copyfileobj(testcase_stream, testcase_stage_file, length=copy_buffer_size)

                        try:
                            with zipfile.ZipFile(testcase_stage_path, 'r') as testcase_zip:
                                valid_files = self._filter_valid_archive_files(testcase_zip.namelist())
                        except zipfile.BadZipFile:
                            reason = _('Invalid testcase archive %(archive)s.') % {
                                'archive': testcase_archive,
                            }
                            report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                            autoproblem_logger.warning(
                                'Skipping statement file %s: invalid testcase archive %s',
                                statement_filename,
                                testcase_archive,
                            )
                            continue

                        testcase_pairs = self._detect_testcase_pairs(valid_files)
                        if not testcase_pairs:
                            reason = _('Could not detect matching input/output testcase pairs in %(archive)s.') % {
                                'archive': testcase_archive,
                            }
                            report['skipped'].append({'file': statement_filename, 'code': problem_code, 'reason': reason})
                            autoproblem_logger.warning(
                                'Skipping statement file %s: no recognizable testcase pairs in %s',
                                statement_filename,
                                testcase_archive,
                            )
                            continue

                        checker_stage_path = None
                        checker_language = self._detect_checker_language(checker_filename) if checker_filename else None
                        checker_storage_name = None
                        if checker_path and checker_language:
                            checker_stage_path = os.path.join(staging_dir, '%05d_%s' % (index, checker_filename))
                            with archive.open(member_name_map[checker_path], 'r') as checker_stream, \
                                    open(checker_stage_path, 'wb') as checker_stage_file:
                                shutil.copyfileobj(checker_stream, checker_stage_file, length=copy_buffer_size)
                            checker_storage_name = '%s/%s' % (problem_code, checker_filename)

                        markdown_content = ''
                        if markdown_path:
                            with archive.open(member_name_map[markdown_path], 'r') as markdown_statement_file:
                                markdown_content = markdown_statement_file.read().decode('utf-8-sig', errors='replace')

                        problem_name, problem_statement = self._parse_markdown_statement(markdown_content, problem_code)

                        pdf_stage_path = None
                        pdf_filename = None
                        if pdf_path:
                            pdf_filename = posixpath.basename(pdf_path)
                            pdf_stage_path = os.path.join(staging_dir, '%05d_%s' % (index, pdf_filename))
                            with archive.open(member_name_map[pdf_path], 'r') as pdf_stream, \
                                    open(pdf_stage_path, 'wb') as pdf_stage_file:
                                shutil.copyfileobj(pdf_stream, pdf_stage_file, length=copy_buffer_size)
                            self._validate_pdf_stage_file(pdf_stage_path, pdf_filename)

                        prepared_problems.append({
                            'file': statement_filename,
                            'code': problem_code,
                            'name': problem_name,
                            'statement': problem_statement,
                            'has_pdf_statement': bool(pdf_stage_path),
                            'pdf_stage_path': pdf_stage_path,
                            'pdf_filename': pdf_filename,
                            'testcase_pairs': testcase_pairs,
                            'testcase_valid_files': valid_files,
                            'testcase_stage_path': testcase_stage_path,
                            'testcase_storage_name': '%s/%s' % (problem_code, testcase_basename),
                            'checker_stage_path': checker_stage_path,
                            'checker_storage_name': checker_storage_name,
                            'checker_filename': checker_filename,
                            'checker_language': checker_language,
                        })

                created_problem_payloads = []

                # Keep the transaction short: only database inserts/updates live in this block.
                with transaction.atomic():
                    upload_started_at = timezone.now()
                    for index, prepared_problem in enumerate(prepared_problems):
                        with revisions.create_revision(atomic=False):
                            problem = Problem.objects.create(
                                code=prepared_problem['code'],
                                name=prepared_problem['name'],
                                description=prepared_problem['statement'],
                                time_limit=1,
                                memory_limit=262144,
                                points=1,
                                partial=True,
                                group=default_group,
                                submission_source_visibility_mode=SubmissionSourceAccess.FOLLOW,
                                testcase_visibility_mode=ProblemTestcaseAccess.AUTHOR_ONLY,
                                # Keep the natural A-to-Z package order stable in date-based views.
                                date=upload_started_at + timedelta(microseconds=index),
                            )
                            self.assign_problem_ownership(problem)
                            problem.types.add(default_type)
                            problem.allowed_languages.set(allowed_languages)

                            problem_data = ProblemData.objects.create(problem=problem)
                            update_fields = []
                            problem_data.zipfile.name = prepared_problem['testcase_storage_name']
                            update_fields.append('zipfile')

                            if prepared_problem['checker_storage_name'] and prepared_problem['checker_language']:
                                problem_data.custom_checker.name = prepared_problem['checker_storage_name']
                                problem_data.checker = 'bridged'
                                problem_data.checker_args = json.dumps({
                                    'files': prepared_problem['checker_filename'],
                                    'lang': prepared_problem['checker_language'],
                                    'type': 'default',
                                })
                                update_fields.extend(['custom_checker', 'checker', 'checker_args'])

                            problem_data.save(update_fields=tuple(update_fields))

                            cases = [
                                ProblemTestCase(
                                    dataset=problem,
                                    order=case_index,
                                    type='C',
                                    input_file=input_file,
                                    output_file=output_file,
                                    points=1,
                                    is_pretest=False,
                                    is_sample=False,
                                )
                                for case_index, (input_file, output_file) in enumerate(prepared_problem['testcase_pairs'], start=1)
                            ]
                            ProblemTestCase.objects.bulk_create(cases)

                            revisions.set_comment(_('Bulk-created from /autoproblem upload'))
                            revisions.set_user(self.request.user)

                        prepared_problem['problem'] = problem
                        prepared_problem['problem_data'] = problem_data
                        created_problem_payloads.append(prepared_problem)

                        report['created'].append({
                            'file': prepared_problem['file'],
                            'code': prepared_problem['code'],
                            'name': prepared_problem['name'],
                            'url': reverse('problem_detail', args=[prepared_problem['code']]),
                        })

                for created_problem in created_problem_payloads:
                    if created_problem.get('pdf_stage_path'):
                        with open(created_problem['pdf_stage_path'], 'rb') as pdf_statement_file:
                            created_problem['problem'].pdf_url = pdf_statement_uploader(
                                File(pdf_statement_file, name=created_problem.get('pdf_filename'))
                            )
                        created_problem['problem'].save(update_fields=('pdf_url',))

                    with open(created_problem['testcase_stage_path'], 'rb') as testcase_file:
                        problem_data_storage.save(created_problem['testcase_storage_name'], File(testcase_file))

                    if created_problem['checker_storage_name'] and created_problem['checker_stage_path']:
                        with open(created_problem['checker_stage_path'], 'rb') as checker_file:
                            problem_data_storage.save(created_problem['checker_storage_name'], File(checker_file))

                    ProblemDataCompiler.generate(
                        created_problem['problem'],
                        created_problem['problem_data'],
                        created_problem['problem'].cases.order_by('order'),
                        created_problem['testcase_valid_files'],
                    )
                    self.post_problem_created(created_problem['problem'])

        except (zipfile.BadZipFile, OSError, ValueError) as e:
            return generic_message(self.request, _('Invalid upload package'), str(e), status=400)

        contest_formset = None
        add_existing_contest_form = None
        can_create_contest = self._can_create_regular_contest() or self._can_create_any_organization_contest()
        if report['created'] and can_create_contest:
            contest_formset = self._get_contest_formset(report['created'], target_organization=self.target_organization)
            contest_org_prefix_map_json = json.dumps(self._build_contest_org_prefix_map(contest_formset))
        else:
            contest_org_prefix_map_json = json.dumps({})

        if report['created']:
            add_existing_contest_form = self._get_add_existing_contest_form(report['created'])

        return self.render_to_response(self.get_context_data(
            form=form,
            report=report,
            contest_formset=contest_formset,
            add_existing_contest_form=add_existing_contest_form,
            contest_org_prefix_map_json=contest_org_prefix_map_json,
            contest_created_success=False,
            contests_created_in_submit=0,
            contest_create_error=None,
            add_existing_success=False,
            add_existing_added_count=0,
            add_existing_skipped_count=0,
            add_existing_error=None,
            add_existing_contest=None,
            created_contests=[],
            created_contest_keys='',
            available_problem_codes_csv=','.join(item['code'] for item in report['created']),
            contest_action_mode='create_new',
        ))


class ProblemUpdatePolygon(ProblemImportPolygon, ProblemMixin, SingleObjectMixin):
    title = gettext_lazy('Update problem from Codeforces Polygon package')

    def get_object(self, queryset=None):
        problem = super().get_object(queryset)
        if not problem.is_editable_by(self.request.user):
            raise PermissionDenied()
        return problem

    def get_form_kwargs(self):
        kwargs = super().get_form_kwargs()
        kwargs['code'] = self.object.code
        return kwargs

    def dispatch(self, request, *args, **kwargs):
        self.object = self.get_object()
        return super().dispatch(request, *args, **kwargs)


class ProblemEdit(ProblemMixin, TitleMixin, UpdateView):
    template_name = 'problem/editor.html'
    model = Problem
    form_class = ProblemEditForm

    def get_title(self):
        return _('Editing problem {0}').format(self.object.name)

    def get_content_title(self):
        return mark_safe(escape(_('Editing problem %s')) % (
            format_html('<a href="{1}">{0}</a>', self.object.name,
                        reverse('problem_detail', args=[self.object.code]))))

    def get_object(self, queryset=None):
        problem = super(ProblemEdit, self).get_object(queryset)
        if not problem.is_editable_by(self.request.user):
            raise PermissionDenied()
        return problem

    def get_solution_formset(self):
        if self.request.POST:
            return ProposeProblemSolutionFormSet(self.request.POST, instance=self.get_object())
        return ProposeProblemSolutionFormSet(instance=self.get_object())

    def get_language_limit_formset(self):
        if self.request.POST:
            return LanguageLimitFormSet(self.request.POST, instance=self.get_object(),
                                        form_kwargs={'user': self.request.user})
        return LanguageLimitFormSet(instance=self.get_object(), form_kwargs={'user': self.request.user})

    def get_context_data(self, **kwargs):
        data = super().get_context_data(**kwargs)
        data['lang_limit_formset'] = self.get_language_limit_formset()
        data['solution_formset'] = self.get_solution_formset()
        return data

    def get_form_kwargs(self):
        kwargs = super(ProblemEdit, self).get_form_kwargs()
        # Due to some limitation with query set in select2
        # We only support this if the problem is private for only
        # 1 organization
        if self.object.organizations.count() == 1:
            kwargs['org_pk'] = self.object.organizations.values_list('pk', flat=True)[0]

        kwargs['user'] = self.request.user
        return kwargs

    def save_statement(self, form, problem):
        statement_file = form.files.get('statement_file', None)
        if statement_file is not None:
            problem.pdf_url = pdf_statement_uploader(statement_file)

    def post(self, request, *args, **kwargs):
        self.object = self.get_object()
        form = self.get_form()
        form_lang_limit = self.get_language_limit_formset()
        form_edit = self.get_solution_formset()
        if form.is_valid() and form_edit.is_valid() and form_lang_limit.is_valid():
            with revisions.create_revision(atomic=True):
                problem = form.save()
                self.save_statement(form, problem)
                problem.save()
                form_lang_limit.save()
                form_edit.save()

                revisions.set_comment(_('Edited from site'))
                revisions.set_user(self.request.user)

            return HttpResponseRedirect(reverse('problem_detail', args=[self.object.code]))

        return self.render_to_response(self.get_context_data(object=self.object))

    def dispatch(self, request, *args, **kwargs):
        try:
            return super(ProblemEdit, self).dispatch(request, *args, **kwargs)
        except PermissionDenied:
            return generic_message(request, _("Can't edit problem"),
                                   _('You are not allowed to edit this problem.'), status=403)


class ProblemEditTypeGroup(PermissionRequiredMixin, ProblemMixin, TitleMixin, UpdateView):
    template_name = 'problem/type-group-editor.html'
    model = Problem
    form_class = ProblemEditTypeGroupForm
    permission_required = 'judge.edit_type_group_all_problem'

    def get_title(self):
        return _('Editing problem {0}').format(self.object.name)

    def post(self, request, *args, **kwargs):
        self.object = self.get_object()
        form = self.get_form()
        if form.is_valid():
            with revisions.create_revision(atomic=True):
                problem = form.save()
                problem.save()

                revisions.set_comment(_('Edited types/group from site'))
                revisions.set_user(self.request.user)

            return HttpResponseRedirect(reverse('problem_detail', args=[self.object.code]))

        return self.render_to_response(self.get_context_data(object=self.object))

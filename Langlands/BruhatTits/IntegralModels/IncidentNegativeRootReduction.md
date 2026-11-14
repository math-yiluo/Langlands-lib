# Vanishing of negative root composites from positive reduction

This internal deduction assumes the existing proposition
`UnramifiedRootPositiveReductionStatement`. It does not prove that proposition.
For two characterized neutral zero-fixer models, a compatible split integral
apartment torus and a target reductive quotient, it proves that every actual
source-root composite whose root is strictly negative on the specified
cocharacter displacement is the zero scheme morphism.

The initial geometric lemma needs no facet incidence: the root fixer of a
subset containing the translated endpoint lies in the strictly positive
filtration at the original endpoint. This follows from the exact
filtration-translation identity and inclusion of a positive-depth filtration
in the zero-plus filtration. The target apartment subset is nonempty and
bounded under every affine functional. No boundedness of the source subset is
needed for this negative comparison.

The root model's generic integral-point image equals the actual source root
fixer. Naturality of integral sections and the canonical root-map square
identify its image with the corresponding target root section. The assumed
positive-reduction proposition therefore places each reduction in the target
radical, using the original endpoint as its existential positive point. The
represented quotient kills these radical points.

`IntegralModel.specialFibreHom_eq_zero_of_reduction` supplies the scheme-level
step. Smooth Henselian reduction lifts every residue-field rational point to
an integral section. The source special fibre is smooth, hence reduced and
locally of finite type. Over the algebraically closed residue field of the
actual maximal-unramified integers, equality on rational points then determines
the morphism into the separated affine quotient. Thus the conclusion holds on
all scheme tests, including infinitesimal tests.

`rootTargetReductiveQuotientKernelIsoOfEvalNeg` identifies the full
scheme-theoretic kernel with the original root special fibre, using the
existing `Langlands.GroupScheme.zeroKernelIso` from
[VectorScalarKernel](../../GroupScheme/VectorScalarKernel.md). The distinctly
named `kernelIsoOfEqZero` transports that isomorphism along equality with zero;
`smooth_kernel_of_eq_zero` transfers smoothness from the source. Consequently the full
negative root-composite kernel is smooth.

The general `Lie.targetMapLinear_eq_zero_of_eq_zero` proves that a zero
homomorphism has zero differential on every test algebra, directly by
postcomposition of dual-number points. The negative root differential therefore
has zero range. Smoothness of the full original kernel then permits the
schematic-image Lie comparison, giving zero range for the inclusion of the
actual schematic image as well. The root source is smooth and connected by the
integral-root construction, and the supplied reductive quotient is smooth and
affine, as required for that comparison.

These are internal deductions from the cited Library interfaces, rather than
new source claims. All data and results retain arbitrary universe `u`. This
module does not assert smoothness of the full ambient incident kernel or the
complete facet sign formula.

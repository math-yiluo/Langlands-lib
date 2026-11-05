# Finite adelic action on actual analytic coefficient tensor cohomology

This internal construction starts from the actual reduced tensor Lie module,
horizontal differential and quotient cohomology in
`ArchimedeanAlgebraicCoefficientAnalyticHorizontal`. It uses the original finite
adelic translation representation of `S.Space ⊗[ℂ] AnalyticSpace e ρ`, which
translates the automorphic factor and acts trivially on the coefficient factor.
The already constructed `tensorHorizontalFiniteRepresentation` acts on the
original full-compact-equivariant horizontal cochains by postcomposition.

`tensorAnalyticFiniteReducedLieHom` bundles the existing proved commutation
of finite translation with the reduced diagonal tensor Lie action.
Coefficient differential functoriality for this actual Lie module map proves
`tensorAnalyticHorizontalDifferential_finite`. Thus differential commutation
is a theorem about the original actions, not a supplied chain-action premise.
`tensorAnalyticHorizontalDifferentialIntertwiner` packages the actual
horizontal differential as a finite adelic intertwiner, with its underlying
linear map identified explicitly.

The published horizontal cohomology action construction now applies with that
proved commutation law. It restricts the same original finite translations to
the actual cycle kernels, proves preservation of the actual differential-image
boundaries, and descends to the existing quotient. These are exposed as
`tensorAnalyticHorizontalCyclesFiniteRepresentation` and
`tensorAnalyticHorizontalCohomologyFiniteRepresentation`. The cycle application
law retains the original translated cochain. The class application law says a
translated class is represented by that same translated cycle.

`tensorAnalyticHorizontalClassFiniteIntertwiner` equips the already constructed
cycle-to-cohomology projection with finite adelic equivariance. Its
`toLinearMap` lemma identifies it with the original quotient projection. No
new quotient type or replacement class relation is introduced.

The number-field universe remains independent of the small finite selected
embedding and coefficient indices. Both complex-place orientations, the entire
original coefficient carrier and empty finite indices are retained.
`NeZero n` is explicit for the existing horizontal differential and cohomology
construction; the reduced Lie module map itself has no positive-rank
requirement. Every cohomology degree is included. No topology or smoothness
claim about the quotient representation is made here.

The provenance is internal specialization of the actual tensor finite action,
coefficient differential functoriality and the published horizontal quotient
action construction, with its differential commutation premise proved.
No new original-literature correspondence is claimed.

# Compact approximation for actual coefficient-model vectors

Author: Worker 396.

This internal derived helper connects the compact induced approximation in
`RankOneMatrixFunctionalEquationComparisonCompactApproximation` to actual
Whittaker coefficient models. Its comparison theorem is conditional on a
compact-function identity and genuine integrability of both weighted limiting
restrictions.

For a representation of a topological group, a subgroup character and an
equivariant functional, `modelSmoothFunction` sends each vector of the actual
coefficient image to scalar character smooth induction. Smoothness of the
original representation supplies a single open right stabilizer through
`Whittaker.model_isSmooth`. The covariance is precisely the defining covariance
of the coefficient function. The inclusion preserves every pointwise value.
`modelSmoothInclusion` bundles this construction as an injective intertwining
map; its linearity, equivariance and injectivity follow by evaluating functions.
No irreducibility, nonvanishing, or identification of the original representation
with its image is assumed.

`weighted_model_integral_eq_of_compact` applies the compact quotient reduction to
this included function. Its conclusion uses the unchanged actual model
function. The supplied measures, maps into the group and complex weights are
unchanged. In particular, integrability of the limiting restrictions is an
explicit hypothesis on each side.

`weighted_glModel_integral_eq_of_compact` specializes this result to the actual
upper-unipotent subgroup of `GL_(n+1)` over any canonical p-adic field, including
`n = 0`. The field and representation-module universes are independent. The
proof installs the canonical topology and valuative relation, derives the
nonarchimedean group structure from
`valuativeGeneralLinearNonarchimedean`, and uses the published local compactness
and sigma compactness certificates. Closedness is
`GeneralLinear.UpperUnipotent.isClosed`. These are all local instances, so the
theorem requires no additional topology or countability premises. Every supplied
unitary additive character is retained.

The construction is internal: its provenance is the published coefficient-image
smoothness theorem, scalar-character representation, smooth induced-function
constructor and p-adic matrix topology results, together with the compact
approximation helper. This file proves the model adapter and compact-support
reduction only; it does not establish the compact Fourier identity, its weighted
convergence hypotheses or a gamma functional equation.

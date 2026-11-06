# The common compact normalization in semidirect source coordinates

Worker 200. This is an internal comparison of the published
`SubgroupCompactOpenHaar` and `SemidirectSourceGamma` constructions.

Waldspurger, *La formule de Plancherel pour les groupes p-adiques*
(2003), I.1, printed p.240 / PDF p.6, fixes the Haar measure on each closed
algebraic subgroup by giving its intersection with the same special compact
subgroup mass one. Formula (2) uses the Levi and radical measures together,
and formula (3) defines the resulting gamma. This module compares the
existing generic measures at that exact scale; it does not construct a
special compact subgroup or prove its source decomposition properties.

For an actual semidirect decomposition `P = M U`,
`semidirect_compact_split_iff` proves that the statement
`m u ∈ K ↔ m ∈ K ∧ u ∈ K` is equivalent to the actual Levi projection
carrying `P ∩ K` into `M ∩ K`. In the forward direction apply the
factorization to `p = projection(p) (projection(p)⁻¹ p)`. In the reverse
direction projection stability gives membership of `m`, and multiplication
by its inverse gives membership of `u`. This is an algebraic equivalence,
not a proof of either property for a chosen geometric compact subgroup.

The remaining comparisons use a locally compact, second countable
topological group in an arbitrary universe, its Borel measurable space,
closed subgroups `P`, `M`, `U`, continuous semidirect Levi projection, and
a compact open subgroup `K`. All subgroup measures are the existing
`Haar.subgroupCompactOpenHaar K hK`, not restrictions of ambient Haar.

`semidirectSourceParabolicMeasure_subgroupHaar_regular` maps the product
of the two existing regular measures through the canonical semidirect
homeomorphism. If the displayed compact factorization holds,
`semidirectSourceParabolicMeasure_eq_subgroupHaar` proves that this product
pushforward equals the existing mass-one Haar measure on the original
`P`. The earlier product-Haar theorem gives left invariance, the earlier
compact-mass theorem gives mass one, and regular Haar uniqueness proves
the equality. Local compactness of each factor follows from its
closedness; no extra source measure is selected.

`compactNormalizedSourceGamma` is the already defined `openCellConstant`
using the existing normalized measures on `P` and `V`, for any supplied
closed opposite subgroup `V`. The final theorem rewrites the product
measure by the proved equality and identifies it with
`semidirectSourceGamma` using the existing normalized measures on
`M`, `U`, and `V`. It changes neither the constant nor its Haar scale.

These comparisons do not require an open-cell embedding or conullness
and do not prove those properties. Actual special-compact factorization,
all semistandard rational comparisons, gamma dependence only on the Levi,
root-index products, real-integral convergence, and the main Plancherel
conclusions retain their separate proof obligations. The already
published gamma integration theorems retain their displayed hypotheses.

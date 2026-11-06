# Metrics and supplied-model comparisons under equivariant quotient equivalences

This is an internal construction on the Library's existing reduced building
quotients, for every universe `u`. Both valuation-building data use the same field
`F` and the same group scheme `G`. The equivalence `e` must intertwine the original
`G(F)` actions with the identity on that group. No equivalence is constructed or
assumed to exist unconditionally.

`ValuationBuildingData.MetricRealization.pullback` constructs a complete metric on
the source quotient from a supplied `MetricRealization` on the target quotient.
Its distance between `x` and `y` is exactly the supplied distance between `e x` and
`e y`, as `pullback_dist` records. The construction uses Mathlib's induced metric
and packages `e` as an isometric equivalence to transfer completeness. The inverse
image of a target NPC midpoint satisfies the source NPC inequality because every
distance in that inequality is preserved. Equivariance transfers isometricity of
the original rational-point action. Composing target orbit maps with the inverse
isometry proves continuous source orbit maps. Throughout, the topology on `G(F)`
is exactly `rationalPointTopology F G.X`.

`compactStabilizer_eq_of_equivariant` proves equality of the norm-one point
stabilizers as actual subgroups of the same `G(F)`. The rational common norm kernel
is unchanged, and equivariance and injectivity preserve and reflect the condition
that a group element fixes the specified point. The theorem requires no metric.

`BuildingComparison.pullback` transports an already supplied comparison for the
original integral model `M` to the supplied source building. Its point is exactly
`e.symm D.point`; `pullback_building` and `pullback_point` record these definitional
identities. The source point's vertex and special-point properties remain
explicit premises. The preceding construction transfers the metric fields, and
the exact subgroup equality proves the required equality with `M.integralPoints`.
If that original model image fixes a source point, equivariance maps it to a point
fixed by the same subgroup in the target; target uniqueness and injectivity give
source uniqueness.

The content is derived from the published `MetricRealization`, `BuildingComparison`
and `compactStabilizer` definitions and Mathlib's induced-metric and
isometric-equivalence constructions. There is no new literature assertion.
This helper supplies no building or metric existence theorem, no equivariant
equivalence, no vertex or special-point preservation theorem and no comparison for
an arbitrary supplied model. In particular, the unconditional
`BuildingComparisonStatement` remains a separate proof obligation. The supplied
model, its generic identification and its integral-point image are retained.

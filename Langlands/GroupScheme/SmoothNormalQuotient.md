# Actual smooth normal quotients

`SmoothNormalQuotient i` packages an actual group scheme `Q` over the original
field and a group-scheme homomorphism `G → Q`. The package records that `Q`
is smooth, separated, locally of finite type and quasi-compact, and that the
projection is smooth, scheme-surjective and quasi-compact. Its
`isFppfQuotient` field is the published represented fppf quotient predicate
for the full all-test image of `i`, including the exact scheme-theoretic kernel.

`SmoothNormalQuotient.ofClosedNormal` constructs this data for a smooth closed
normal subgroup `i : N → G` of a smooth affine group over an arbitrary field.
It chooses the published smooth homogeneous scheme quotient with its exact
right-coset fibers on every relative scheme test. Normality permits the
published `NormalQuotient.groupScheme` construction to descend multiplication
and inversion to this same scheme, retaining the original projection.
Its exact represented kernel gives the required fppf quotient predicate.
The target structure morphism is smooth by smooth surjective descent on the
source, applied to the composite with the smooth structure morphism of `G`.
All other recorded properties come from the chosen homogeneous quotient.

`SmoothNormalQuotient.connectedSpace` transfers connectedness of `G` to
the quotient along its continuous surjective scheme map.

This is internal derived quotient data, assembled from the published
`smoothSubgroupQuotientExistence`, `NormalQuotient` and smooth descent interfaces.
The quotient scheme carries the descended group law. No affineness of `Q`
or pseudo-reductivity is asserted here; those remain separate obligations.
The subgroup `N` must be smooth, whereas the more general published
`NormalSubgroupQuotientStatement` permits a nonsmooth normal subgroup.

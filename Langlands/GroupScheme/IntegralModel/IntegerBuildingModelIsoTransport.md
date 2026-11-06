# Original integral-model images on transported integer buildings

This internal construction works over any field `k` with an explicit
integer-valued valuation `v`. Both actual integral models have the same
domain `R` and fraction field `k`; their generic groups can differ.
The affine generic groups, valuation-building data `B`, point `x`, compatible
integral-model isomorphism `e`, and exact source equality
`M.integralPoints = B.oneStabilizer x` are supplied. No local-field or
completeness hypothesis is used.

`Iso.integralPoints_eq_oneStabilizer_mapIso` identifies the original target
model image with the one-group stabilizer of the point transported through
`B.mapIsoReducedBuildingEquiv f`, in exactly `B.mapIso f`.
It rewrites the target image by the existing `Iso.map_integralPoints`,
substitutes the source equality, and applies the exact integer-building
stabilizer-image theorem. The character-valuation kernel and the existing
quotient action are those of the transported building.

`Iso.integralSectionsToOneStabilizer` restricts the codomain of the original
`N.integralPointMap` to that stabilizer. Its underlying rational point is
definitionally the original section image. The surjectivity theorem takes
an arbitrary stabilizer element, uses the exact subgroup equality to put it
in the original model image, and chooses an integral section from its range
witness. Thus the result concerns the supplied target model and its original
generic identification.

`Iso.unique_fixed_mapIso` carries global uniqueness for the original source
model image through the same quotient equivalence. Pull a target fixed point
back, apply equivariance and model-image preservation to prove source fixation,
use the supplied source uniqueness, and then apply the quotient equivalence.
The source subgroup equality is unnecessary for this uniqueness deduction.
The existing `isVertex_mapIso_iff` and `isSpecialPoint_mapIso_iff` transport
those geometric predicates through this exact quotient map as well.

The `ofGroupIso` adapters allow any actual abstract integral isomorphism.
They use `M.inducedGenericIso N e`, computed from both original generic
identifications and the actual generic pullback of `e`; they do not assume
compatibility with an independently specified generic map.

The provenance is internal: these are compositions of existing model-image
transport and the actual integer-building isomorphism construction.
The module constructs neither the source building/model comparison nor the
integral isomorphism, and proves no metric or descent existence assertion.
The unconditional `BuildingComparisonStatement` remains a separate obligation.

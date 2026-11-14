# Intrinsic root-point Lie comparisons under torus restriction

This internal prerequisite compares the actual root subgroup inclusion for a
homomorphism of tori with the intrinsic root-point to Lie-weight comparison.
It derives the comparison from represented subgroups and common-weight
homomorphism naturality; it makes no new literature claim.

`IsWeightVectorCoordinates.restrict` keeps the same vector coordinates and
restricts their weight along the torus homomorphism, on every test scheme.
`rootGroupPointsTorusInclusion` is the existing all-test root subgroup inclusion
restricted to rational points. Its underlying ambient point is unchanged.

`subgroupAction_torusInclusion` constructs the smaller torus equivariance of
the actual inclusion between any two representatives, by cancelling the
representing monomorphism and computing ambient conjugation.

Over a field, for two split tori acting on a smooth affine group,
`rootPointLieEquiv_torusInclusion` states that inclusion into the root group
of the restricted character preserves the intrinsic ambient Lie vector.
Both characters must be nonzero and have no higher positive roots for their
respective torus actions. The proof chooses affine representatives, restricts
the original vector coordinates, and applies the actual differential
naturality for a homomorphism of the same nonzero weight. The composite of
the representing inclusion with the subgroup inclusion is the original
representing morphism, so the two differentials give the same ambient vector.

`rootPointLieEquiv_rootPointsProduct` applies this identity to an ordered
finite product of points from possibly different original root groups, all
with the same restricted character. If an actual relative root point has
that ambient ordered product as its value, its intrinsic Lie vector is the
sum of the original root-point Lie vectors. Every original character and
the restricted character must be nonzero and have no higher positive roots.
No injectivity of the root enumeration, positivity of its length, or
commutativity assumption on the ambient group is needed. The empty product
is included. The proof lifts each factor by the subgroup inclusion, compares
the relative point with their product, and applies additivity of the intrinsic
comparison to the associated list sum.

These field-level comparisons assert no integral-model or special-fibre kernel
property.

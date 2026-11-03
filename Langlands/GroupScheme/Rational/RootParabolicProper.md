# Actual root points outside opposite dynamic parabolics

For a smooth affine group scheme over any field, a split torus acting by
conjugation, an actual relative root `a`, and a cocharacter `ν` with
`⟨a,ν⟩ > 0`, this module constructs an actual nonidentity point of the
intrinsic `a` root subgroup over the dual numbers of the original field.
This point lies outside the actual dynamic parabolic for `-ν`. Hence that
parabolic is a proper subgroup functor.

The provenance is internal. The exact tangent image in
[`RootSubgroupLieImage`](RootSubgroupLieImage.md) contains the weight
space of `a`: the positive cyclic tail includes `a` itself. By the
definition of an actual relative root, that weight space is nonzero.
Choose a nonzero vector there and regard its underlying Lie-kernel point
as a point over the dual numbers. Intrinsic tangent membership is exactly
root-subgroup membership of this point. A nonzero Lie vector has a
nonidentity underlying group point.

The published all-test separation in
[`RootSubgroupSeparation`](RootSubgroupSeparation.md) says that a root
point also belonging to the dynamic parabolic for a negatively pairing
cocharacter must be the identity. It therefore excludes the constructed
point from that parabolic. `rootPointOutsideNegativeParabolic` selects the
point together with these properties, and `negativeParabolic_ne_top`
deduces that the parabolic functor cannot equal the whole group functor.

The result retains arbitrary universe, field and characteristic scope.
It requires no reductivity, connectedness, maximality of the split torus,
root-system structure, or nonidentity rational root point. It proves
properness as a strict inclusion of all-test subgroup functors, not a
properness assertion about the parabolic's morphism to the base. It does
not supply opposite factor-pair existence or prove
`RootRankOneFactorizationStatement`.

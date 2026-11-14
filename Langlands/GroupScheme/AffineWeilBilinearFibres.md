# Geometrically connected fibres of actual restricted bilinear groups

This derived helper proves geometric connectedness of the structure map of
an actual affine Weil restriction of a bilinear coordinate group.

Let `A` be a commutative ring and `B` a finite projective commutative
`A`-algebra. For a finite index type `I` and arbitrary bilinear coefficients
`c : I → I → B`, the theorem
`AffineWeilBilinear.restriction_geometricallyConnected` asserts
`GeometricallyConnected` for
`(AffineWeil.groupScheme A B (BilinearCoordinate.groupScheme _ c)).X.hom`.
All the types belong to an arbitrary common universe `u`. Neither a basis
of `B` over `A` nor a local-ring or field hypothesis on `A` is required.

The proof applies Mathlib's field-test criterion
`geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms` to the
isomorphism-invariant property `ConnectedSpace`. For each `A`-algebra
field `k`, the actual fibre group is identified by `restrictionFibreIso`
with the restriction over `k` of the bilinear group whose coefficient
algebra is `k ⊗[A] B` and whose coefficients are the images of `c`.
This finite-dimensional `k`-algebra has `Module.finBasis`, so
`AffineWeilBilinear.properties` proves connectedness of that restricted
group. `smooth_connected_of_groupIso` transfers connectedness to the
actual pullback fibre. The field tests include all field extensions of
all residue fields, giving the stated geometric connectedness.

The argument uses actual scheme and group-scheme isomorphisms. It permits
nonreduced fibre algebras. Its provenance is the field-test consequence of
the existing `AffineWeilBilinearSpecialFibre` and `AffineWeilBilinear`
constructions; it introduces no independent source assertion.

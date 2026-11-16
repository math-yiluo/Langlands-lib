# Smoothness of a homomorphism from its open-cell restriction

This is an internal consequence of the published open-product geometry and
smooth source-descent theorems. It proves smoothness of the conditional
coroot-cell extension over every coefficient ring. It does not establish
existence of a compatible cell map or prove its negative-simple relation.

The generic theorem `smooth_of_smooth_openCell` takes a reductive group `G`
over an arbitrary scheme `S`, a smooth group `H` over `S`, a homomorphism
`q : G ⟶ H`, and an open immersion `j : C ⟶ G.X` containing a supplied unit
point. It assumes that the composite `j ≫ q` is smooth, and proves that `q`
is smooth.

Reductivity and the open immersion make `C` smooth over `S`.
`ReducedBaseSmooth.smooth_tensorHom_comp_mul` proves that multiplication
`C × C ⟶ G` is smooth. The source group has smooth connected residue-field
fibres, so `range_tensorHom_comp_mul_eq_univ` proves this multiplication map
surjective because the open contains the unit. These two published product
lemmas have no noetherian or reducedness assumption.

The group-homomorphism law identifies the composite `C × C ⟶ G ⟶ H` with the
two smooth cell restrictions followed by multiplication in `H`. A product
of smooth maps is smooth by base change and composition, and multiplication
of the smooth group `H` is smooth. The published theorem
`Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp`
then descends smoothness through `C × C ⟶ G`, without a quasi-compactness or
finite-presentation premise.

`smooth_of_corootCellProjection` specializes this result to a homomorphism
whose restriction to the open split cell is exactly `corootCellProjection`.
For finite coordinate and root index types, the quotient is a split torus
and hence smooth; the cell projection is smooth by the preceding module.
`smooth_corootCellExtension` applies this to the actual glued homomorphism.
Its compatibility premise remains explicit.

`smoothCorootCellExtension` returns that actual homomorphism together with
its exact torus restriction, smoothness and surjectivity as a subtype. This
packages the map's established properties for the separate full-kernel
comparison; no semisimplicity conclusion is included in this package.

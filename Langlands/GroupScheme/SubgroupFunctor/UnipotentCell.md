# Open cells with unipotent factors

This internal construction concerns actual multiplication morphisms of group
schemes over an algebraically closed field. The ambient group is connected,
affine and locally of finite type. Both source groups are smooth affine and
unipotent. No normality, commutativity, or closedness of their homomorphisms
into the ambient group is assumed.

`isClosed_range_cellMultiplication` proves that their two-factor multiplication
has closed topological image. It expresses multiplication as the orbit map of
the product group acting by left multiplication and inverse right
multiplication, after inverting the second coordinate. It then applies the
published closed-orbit theorem for unipotent groups.

If this same multiplication is an open immersion,
`isIso_cellMultiplication_of_unipotent` proves that it is an isomorphism of
schemes over the field. Its image is nonempty, open and closed, and the ambient
group is connected. `unipotentCellIso` packages that isomorphism and
`unipotentCellIso_hom` identifies its forward map with the supplied
multiplication.

The provenance is internal composition of the existing subgroup-product
action, unipotent closed-orbit theorem, inversion comparison, connected-space
criterion, and the characterization of a surjective open immersion as an
isomorphism. This unit does not assert that an arbitrary dynamic cell is
surjective; its open-immersion and unipotence hypotheses must be established
for the actual factors to which it is applied.

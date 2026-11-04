# Actual additive coordinate maps and their full kernels

This internal construction gives actual homomorphisms to the one-dimensional
vector group on the coordinate-refined closed subgroup schemes and their
full inverse images along matrix representations. The base is any
commutative ring.

`refinedPoints` identifies points of a refined subgroup scheme over every
test scheme with the original refined matrices over its ring of global
sections. `refinedCoordinateNatTrans` restricts the additive layer-coordinate
homomorphism to these matrices over coefficient algebras. Its naturality
uses the coefficient-ring formula from the matrix filtration.
`refinedCoordinate` is the actual group-scheme homomorphism induced by
that transformation. It has the stated matrix-entry formula on all tests.

`filtrationCoordinate` composes the inverse-image projection with this
coordinate homomorphism. The cartesian square identifies its all-test
formula with the original matrix-layer entry in the source group.

For a position `j = i + a + 1`,
`range_kernel_filtrationCoordinate` proves that the range in the original
group scheme of the full actual kernel is exactly the next refined term.
The proof uses `mem_range_kernelι_iff`, the all-test coordinate formula
and the exact successor zero-locus in the matrix filtration. Thus no
reduced or rational-point kernel is substituted.

The construction does not assert quotient existence, that a quotient
embeds as a closed subgroup of the additive group, character-action
descent, or splitting. Those are later steps in the tower construction.

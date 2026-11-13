# H¹ coordinates from an actual universal rigidified Picard family

Author: Worker 327.

This derived internal construction combines published tangent, dimension,
and ample-line-bundle results. Its geometric input is an **actual supplied**
rigidified universal Picard family `L` on a parameter scheme `P`, with
`LocallyOfFiniteType P.hom`. Neither the family nor its parameter is
constructed here.

`structureSheafH1Finrank_eq_of_picardOriginLowerBound` works over any field
`k`. For an abelian scheme `A` of relative dimension `g`, it assumes that
the origin stalk of `P` has Krull dimension at least `g`. The published
`fieldUniversalRigidifiedPicardTangentH1` identifies the tangent module of
`P` at the trivial-family section with actual structure-sheaf H¹. The
published `fieldPointTangentLocalRegularity` identifies the tangent
dimension with the embedding dimension of that stalk. Krull's height
theorem bounds the stalk dimension by its embedding dimension, giving
`g ≤ dim H¹`. The published independent bound
`fieldStructureSheafH1DimensionBound` gives the reverse inequality.

`algClosed_structureSheafH1Finrank_eq_of_universalPicard` assumes also
that `k` is algebraically closed. It supplies the origin lower bound
using an ample line bundle on `A`, finiteness of its rational translation
stabilizer, and
`algClosedFieldRigidifiedPicardOriginDimensionLowerBound`. Thus, under
the stated universal-family input, actual H¹ has dimension `g`.

`rigidifiedPicardH1CoordinateEquiv` constructs a noncanonical linear
equivalence from that H¹ to `Fin g → k` by the dimension equality and
finite-dimensionality.

The proof uses the ordinary universal rigidified Picard family only as an
explicit input. It does not prove its existence, a cohomological exterior
description, or formulas for multiplication pullback. It does not use the
six Picard/dual-scheme routes excluded by Task 6105, a proof of
`FieldH2PrimitiveInjectivityStatement`, or any consequence of such a
proof. Its provenance consists of the imported published results and the
stated local-dimension argument; no additional external theorem is invoked.

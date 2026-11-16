# Ambient matrix cell points under a change of base

This internal construction uses the all-test-scheme general-linear point
comparison and the represented block subgroup functors to compare the explicit
ambient matrix cells over two commutative rings. The supplied morphism is
`a : Spec S → Spec R`; no flatness or field hypothesis is imposed.

For a test scheme over `Spec S`, an old-base general-linear point is an
invertible matrix in its global sections. The same matrix defines a new-base
point through the inverse of `GeneralLinear.pointsEquiv`. This construction
keeps the matrix exactly.

The block-unipotent and block-Levi conditions are equations on this same
matrix and the fixed integer weights. The represented subgroup point
equivalences therefore supply actual lifts of old-base block points to the
new-base block schemes. The companion equalities say that their inclusions
into the new general-linear group have the original matrices.

For supplied integral Chevalley data, `ambientCellExtend` lifts the negative
block-unipotent, block-Levi and positive block-unipotent factors, in the same
association as `ambientCellSpace`. Expanding the triple multiplication and
using the three factor identities proves that restriction of its matrix
product is the original old-base matrix product. This is an equality of
morphisms on the entire test scheme, with no restriction to rational points.

The construction supplies compatible ambient points for subsequent schematic
descent arguments. It does not identify an integral closure with the ordered
cell or prove integral reductivity.

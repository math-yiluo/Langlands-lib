# Proof of `Langlands.GroupScheme.GeneralLinear.BlockShapeLimitStatement`

This module proves the published proposition `Langlands.GroupScheme.GeneralLinear.BlockShapeLimitStatement` (module `Langlands.GroupScheme.Dynamic.GeneralLinearStatement`) at every universe `u`. The statement says that for the standard cocharacter of a block shape of `GL_n` over every commutative ring, the limit of the conjugation orbit exists exactly on the block upper triangular points, and equals their block diagonal part.

The theorem is `Langlands.GroupScheme.GeneralLinear.blockShapeLimit : BlockShapeLimitStatement.{u}`, with no hypotheses.

## Proof

The proof term is the fifth of the five components of the published conjunction `GeneralLinear.dynamicStatement : GeneralLinear.DynamicStatement` (projection `.2.2.2.2`).

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.GeneralLinear.dynamicStatement` (module `Langlands.GroupScheme.Dynamic.GeneralLinearProof`)

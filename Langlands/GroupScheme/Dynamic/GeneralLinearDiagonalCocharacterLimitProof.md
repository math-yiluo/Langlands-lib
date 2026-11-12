# Proof of `Langlands.GroupScheme.GeneralLinear.DiagonalCocharacterLimitStatement`

This module proves the published proposition `Langlands.GroupScheme.GeneralLinear.DiagonalCocharacterLimitStatement` (module `Langlands.GroupScheme.Dynamic.GeneralLinearStatement`) at every universe `u`. The statement says that for a diagonal cocharacter of `GL_n` over every commutative ring, the limit of the conjugation orbit exists exactly on the block upper triangular points, and equals their block diagonal part.

The theorem is `Langlands.GroupScheme.GeneralLinear.diagonalCocharacterLimit : DiagonalCocharacterLimitStatement.{u}`, with no hypotheses.

## Proof

The proof term is the third of the five components of the published conjunction `GeneralLinear.dynamicStatement : GeneralLinear.DynamicStatement` (projection `.2.2.1`).

The theorem adds no mathematics; it names a combination of published results.

## Published inputs

- `Langlands.GroupScheme.GeneralLinear.dynamicStatement` (module `Langlands.GroupScheme.Dynamic.GeneralLinearProof`)

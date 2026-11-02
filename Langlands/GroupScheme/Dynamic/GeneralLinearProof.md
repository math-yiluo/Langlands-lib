# Dynamic subgroups of `GL_n` for diagonal cocharacters: proof

This module proves `Langlands.GroupScheme.GeneralLinear.DynamicStatement`, the conjunction of the
five statements of `Langlands.GroupScheme.Dynamic.GeneralLinearStatement`.

`dynamicStatement` takes each component from the helper module
`Langlands.GroupScheme.Dynamic.GeneralLinearOrbit`:

- `DiagonalCocharacterDynamicStatement`: `parabolic_diagonalCocharacter`,
  `centralizer_diagonalCocharacter` and `unipotent_diagonalCocharacter`, for every finite index
  type `n`, every `R : CommRingCat` and every `e : n → ℤ`;
- `BlockShapeDynamicStatement`: `parabolic_blockShapeCocharacter`,
  `centralizer_blockShapeCocharacter` and `unipotent_blockShapeCocharacter`, for every ordered
  block shape `B`;
- `DiagonalCocharacterLimitStatement`: `hasLimit_diagonalCocharacter_iff`;
- `DiagonalCocharacterLeviDecompositionStatement`: `leviDecomposition_diagonalCocharacter`;
- `BlockShapeLimitStatement`: `hasLimit_blockShapeCocharacter_iff`.

The Markdown of the helper module describes those proofs. They use the general results of
`Langlands.GroupScheme.Dynamic.Decomposition` on limits and on the decomposition of `P(λ)`. The
mathematics is Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd ed., 2015), Example 2.1.1,
Lemma 2.1.5 and Proposition 2.1.8(2). The implemented route is explicit: block matrices are
scaled by powers of the coordinate of `𝔸¹`, and the converse uses Laurent-polynomial test points.

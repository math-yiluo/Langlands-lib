# A matrix identity for the open cell of the `(1, n)` parabolic

Module `Langlands.Representation.Shahidi.OpenCellBaseMatrix`, namespace
`Langlands.Shahidi.OpenCell.Base`.

For `GL_(1+(t+2))` with indices split as the first index, the middle indices and the last
index, and a column `y = (y', c)`, the module proves two factorizations of `lower(y)`:

- `lower_eq_p0GL_mul` (for `c ≠ 0`): `lower(y) = p₀ · embed(lower(y'/c)) · κ`, where `p₀` is
  upper block triangular with diagonal blocks `c⁻¹` and `[[I, y'], [0, c]]` and entry `1` in the
  corner `(first, last)`, and `κ` differs from the identity only in the rows and columns
  `first`, `last`, where it is `[[0, -1], [1, c⁻¹]]` (over a valued field `κ` is integral when
  `c⁻¹` is, as used in `Langlands.Representation.Shahidi.OpenCellBaseLift`);
- `lower_eq_embed_mul` (no condition on `c`): `lower(y) = embed(lower(y')) · ℓ(c)`, where `ℓ(c)`
  differs from the identity only in the entry `c` at `(last, first)`.

Here `embed` places `GL_(1+(t+1))` in the first `t + 2` indices (`embed g = diag(g, 1)`). The
module also sets up the index bookkeeping (`aI`, `mI`, `lI`, `blk`) and the explicit matrices
`p0Mat`, `kkMat`, `lowerMat`, `lowerLastMat`. The matrix `p0InvMat y` is a two-sided inverse of
`p0Mat y` when the last entry `c` of `y` is nonzero (`p0Mat_mul_inv`, `p0Mat_inv_mul`; for
`c = 0` the first column of `p0Mat y` vanishes); `kkInvMat c` is a two-sided inverse of
`kkMat c` for every `c` (`kkMat_mul_inv`, `kkMat_inv_mul`), and
`lowerLastMat c · lowerLastMat (−c) = 1`.

## Provenance

A direct matrix computation (a rank-one `GL_2` identity in the coordinates `first`, `last`),
used for the recursive computation of the rank-one open-cell integral.

# Points of the dual period group

Module `Langlands.Global.RankinSelberg.DualExpansionPoints`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. It is internal infrastructure for the proof of
premise E' (`DualProjectionWhittakerExpansion`) in `DualProjectionExpansionReduction`.

Provenance: internal. These are explicit matrix identities in `GL_(m+K+1)` used in the rank
induction for the dual expansion. No literature source is cited for them.

Notation: indices of `GL_(m+K+1)` are `0, …, m+K`. The first `m` indices form the `GL_m` block,
`m, …, m+K-1` the middle block, and `m+K` is the last index.

## Matrices

- `xcMat m K x c`: the matrix whose rows `m, …, m+K-1` carry the rectangle `x` (columns `< m`)
  and the column vector `c` (column `m+K`). It squares to zero (`xcMat_mul_xcMat`), and
  `xcMat_add`, `xcMat_zero` give additivity.
- `rowMat m K b`: the matrix whose last row carries `b` in the columns `< m`. It also squares to
  zero. `xcMat_mul_rowMat` computes `xcMat x c · rowMat b = xcMat (outerRect c b) 0`, with
  `outerRect c b (i, j) = c i · b j`.
- `lrMatrix m K A = diag(I_m, A)` as a monoid homomorphism (`lrMatrix_apply` gives its
  entries); `lrGL` is the induced map on invertible matrices.
- `lastColMat d`: the matrix with the column `d` in the last column above the diagonal.

## Points

- `xcPoint F x c = 1 + xcMat x c`, `rowPoint F b = 1 + rowMat b`, `midPoint F u = diag(I_m, u, 1)`
  and `lastColPoint F d = 1 + lastColMat d`, as adelic points (`pointMatrix_*` lemmas give their
  matrices; `point_ext` and `pointMatrix_mul` reduce point identities to matrices).
- Group laws: `xcPoint_mul` (additive in `(x, c)`), `rowPoint_mul`, `midPoint_mul`, `midPoint_one`.
- Commutations: `rowPoint_mul_xcPoint` (moving `rowPoint b` past `xcPoint x c` shears `x` by
  `outerRect c b`), `rowPoint_mul_midPoint`, and `midPoint_mul_xcPoint`, the conjugation
  `diag(I, u, 1) · x̂ĉ = (u·x)^(u·c)^ · diag(I, u, 1)` with `rowMulRect`.
- Row splitting: for a rectangle on `K + 1` rows, `xcPoint_succ_rect` writes
  `xcPoint x 0 = pad(xcPoint (restOfRect x) 0 · rowPoint (rowOfRect x))`.
- `superSum F u` is the sum of the superdiagonal entries of `u ∈ GL_K(𝔸)` and `lastEntry c` the
  last entry of `c`. `superSum_lastColPoint_mul_pad` and `superSum_mul` give their additivity on
  unitriangular points; `midPoint_lastColPoint` and `midPoint_pad` relate the last column of
  `N_(K+1)` to the rank-`K` points.

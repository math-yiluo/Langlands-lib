# Matrix identities for the first-block row split

Author: Worker 1037.

This module collects derived matrix identities used in the coefficient calculation
of JPSS (1983), Section 4.9. They are stated for the published block shape
`succBlockShape m h` with blocks of sizes `a = m 0 + 1` and `b = m 1 + 1`.

## Original small integral

The total rank is `m 0 + (m 1 + 0 + 1) + 1`. `rowSnoc y x` is the `b × a` matrix
with rows `y` followed by the last row `x`; it is the explicit `Fin.snoc` matrix.
`firstBlockEmbedding_mul_lowerRadical_rowSnoc` proves `diag(v, 1) R(y; 0) =
unequalRankMatrix (m 1) 0 v y`. Here the right side is the published block matrix of
the original small integral for the original block `j = m 1`, `k = 0`. The proof
compares the four entry blocks with the published entry formulas for
`appendIdentity` and `rectangularEntries`.

## Splitting and last rows

The next lemmas hold for every two-block total rank:

- `rowSnoc_eq_add` and `lowerRadical_rowSnoc` give `R(y; x) = R(y; 0) R(0; x)`.
- `lastRow_lowerRadical` gives `lastRow R(Z) = (Z_last, η)`.
- `lastRow_firstBlockEmbedding_lowerRadical_mul` gives
  `lastRow(diag(v, 1) R(Z) g) = (Z_last, η) g`.
- `vecMul_join_eta_firstBlockEmbedding` gives `(w, η) diag(v, 1) = (w v, η)`.

## Transformed small integral

The total rank is `m 0 + (0 + m 1 + 1) + 1`. `inverseTranspose_appendIdentity`
proves `diag(g, I)^ι = diag(g^ι, I)`. Then
`weylLong_mul_inverseTranspose_dualMatrix` proves

`w_(t+1) (unequalRankMatrix 0 (m 1) v x · blockWeylAt)^ι = C · diag(w_a v^ι, 1)`,

where `C` is the published block rotation `blockRotation h`. The proof writes
`blockWeylAt` as the published tail-reversal permutation matrix. It then compares
entries in the four block cases, using the published coordinate laws of
`reversePermutation`.

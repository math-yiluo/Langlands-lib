# Trailing principal minors and the Gram determinants of a block lower triangular matrix

Lean module: `Langlands.Representation.Archimedean.RealLeviChartGram`.

This helper module
contains the matrix identities used by the proof of `RealLeviChartIntegrableStatement`
(module `RealLeviChartIntegrable`, see `RealLeviChartIntegrable.md`). It states no proposition of
its own and cites no literature; all its content is elementary linear algebra written for that
proof ("derived"). Unprefixed names below are in the namespace
`Langlands.Archimedean.RealLeviChartGram`. `GramFormula.gram`, `GramFormula.padded`,
`GramFormula.diagonalTail`, `GramFormula.det_padded`, `GramFormula.mul_mul_transpose` and
`GramFormula.gram_mul` are from the Library module `PrincipalSeriesGramFormula`.

All matrices are real. `n`, `a`, `M` are natural numbers, and `Fin n` indexes rows and columns.

## Trailing principal minors

- `padS r S` is the matrix that agrees with `S` at the entries `(p, q)` with `r ≤ p` and
  `r ≤ q` and with the identity matrix elsewhere. `tm r S = det (padS r S)` is the principal
  minor of `S` on the rows and columns `≥ r` (`tm r S = 1` if `r ≥ n`).
- `gram_eq_tm`: `gram r x = tm r (x xᵀ)`. This holds by definition, because `GramFormula.gram r x`
  is the determinant of `x xᵀ` padded in the same way.
- `padS_zero`, `tm_zero`: `tm 0 S = det S`. `padS_one`, `tm_one`: `tm r 1 = 1`.
- `padS_conj`, `tm_conj`: for an upper triangular `T`,
  `padS r (T X Tᵀ) = padded r T · padS r X · (padded r T)ᵀ`, hence
  `tm r (T X Tᵀ) = (diagonalTail r T)² · tm r X`, where `diagonalTail r T = ∏_{p ≥ r} T_pp`. The
  proof compares entries, using `T_pq = 0` for `q < p`. The determinant step is
  `GramFormula.det_padded`.
- `tm_one_add_vecMulVec`: `tm r (1 + y yᵀ) = 1 + ∑_{p ≥ r} y_p²`. Here `padS r (1 + y yᵀ) = 1 + z zᵀ`
  with `z_p = y_p` for `p ≥ r` and `z_p = 0` otherwise, and the matrix determinant lemma
  `det (1 + z zᵀ) = 1 + zᵀ z` is Mathlib's `det_one_add_replicateCol_mul_replicateRow`.
- `padS_one_add`, `tm_pos`, `det_one_add_pos`: if `G` is positive semidefinite, then
  `padS r (1 + G) = 1 + D G D` with `D = diag(1_{p ≥ r})`, which is positive definite. So
  `tm r (1 + G) > 0`, and in particular `det (1 + G) > 0`.

## Gram matrices of column families

For `V : Fin a → Fin M → ℝ`, a family of columns `V_0, …, V_{a-1} ∈ ℝ^M`:

- `colGram j V = ∑_{k < j} V_k V_kᵀ` (`k` ranges over `Fin a`; for `j ≥ a` this is the sum of all
  `V_k V_kᵀ`).
- `posSemidef_colGram`: `colGram j V` is positive semidefinite.
- `colGram_mulVec`: replacing every `V_k` by `T V_k` gives `T · colGram j V · Tᵀ`.
- `colGram_snoc_of_le`, `colGram_snoc_succ`: for the family `Fin.snoc V' u` of length `a' + 1`,
  `colGram j (Fin.snoc V' u) = colGram j V'` for `j ≤ a'`, and
  `colGram (a' + 1) (Fin.snoc V' u) = colGram a' V' + u uᵀ`.

## The block matrix `[[1, 0], [W, B]]`

- `colMat V` is the `M × a` matrix `W` with the columns `V_k`. `blockLower V B` is the
  `(a + M) × (a + M)` matrix `[[1, 0], [W, B]]` for `B` of size `M × M` (the block matrix
  `fromBlocks 1 0 W B`, reindexed by `finSumFinEquiv`).
- `colMat_mul_transpose`: `W Wᵀ = colGram a V`. `colMat_mul_transpose_of`: if `W'` is `W` with
  the columns `k < l` set to zero, then `W Wᵀ - W' W'ᵀ = colGram l V`.
- `blockLower_mul_transpose`: `blockLower V B · (blockLower V B)ᵀ = [[1, Wᵀ], [W, W Wᵀ + B Bᵀ]]`.
- `gram_blockLower_of_le`: for `l ≤ a`, `gram l (blockLower V B) = det (colGram l V + B Bᵀ)`.
  The padded Gram matrix is `[[1, W'ᵀ], [W', W Wᵀ + B Bᵀ]]`, and Mathlib's Schur complement
  formula `det_fromBlocks_one₁₁` gives `det (W Wᵀ + B Bᵀ - W' W'ᵀ)`.
- `gram_blockLower_add`: `gram (a + r) (blockLower V B) = tm r (colGram a V + B Bᵀ)`. The padded
  Gram matrix is block diagonal with blocks `1` and `padS r (W Wᵀ + B Bᵀ)`.
- `gram_blockLower_conj_of_le`: if `κ κᵀ = 1` and `(det T)² = 1`, then for `l ≤ a`,
  `gram l (blockLower (k ↦ T V_k) (T κ)) = det (1 + colGram l V)`. This follows from the two
  previous items, `colGram_mulVec` and `GramFormula.mul_mul_transpose`:
  `colGram l (T V) + T Tᵀ = T (1 + colGram l V) Tᵀ`.
- `gram_blockLower_conj_add`: if `T` is upper triangular and `κ κᵀ = 1`, then
  `gram (a + r) (blockLower (k ↦ T V_k) (T κ)) = gram r (T κ) · tm r (1 + colGram a V)`. This
  follows from `tm_conj` and `GramFormula.gram_mul`, which gives
  `gram r (T κ) = (diagonalTail r T)²`.

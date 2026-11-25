# Integration of the block chart bound, one row at a time

Lean module: `Langlands.Representation.Archimedean.ComplexBlockChartIntegralProof`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It integrates the block chart bound
`ComplexBlockChart.blockChartBound` (`ComplexBlockChartIntegralStatement`) over its first row. As
a consequence it proves the Library statement `ComplexBlockChartIntegrableStatement` as the
theorem `Langlands.Archimedean.complexBlockChartIntegrable`.

Notation: for `X ∈ M_{k×a}(ℂ)`, `colsUpTo X l` and `rowsFrom X j` are the columns `0, …, l` and
the rows `j, …, k−1` of `X`. `colGram X l = Re det(1 + X_{≤l}ᴴ X_{≤l})` and
`rowGram X j = Re det(1 + X^{(j)} X^{(j)ᴴ})`. The bound is
`blockChartBound ε X = ∏_{l<a} colGram X l ^ ε_l · ∏_{j<k} (1 if j = 0, else (rowGram X j)⁻¹)`.
`ComplexParabolicChartBound.partialSq y l = 1 + ∑_{i<l} |y_i|²`. `Fin.cons x X'` is the matrix
with first row `x` and remaining rows `X'`. Unprefixed names below are in the namespace
`Langlands.Archimedean.ComplexBlockChartProof`.

## The statement

`ComplexBlockChartFirstRowStatement`: let `a, k ∈ ℕ` and `ε : Fin a → ℝ` satisfy the tail condition
`∑_{l ≥ j} (ε_l + 1) < 0` for every `j < a`. Then for every `X' ∈ M_{k×a}(ℂ)`,

`∫_{ℂ^a} blockChartBound ε [x; X'] dx = blockChartBound ε X' · C_ε`

as extended nonnegative reals (`ENNReal.ofReal`, lower Lebesgue integral), where
`C_ε = ∫_{ℂ^a} ∏_l partialSq y (l+1)^{ε_l} dy`. It is proved as
`Langlands.Archimedean.complexBlockChartFirstRow`, from `lintegral_cons`.

The module also proves `ComplexBlockChartIntegrableStatement` itself, as
`complexBlockChartIntegrable`, by induction on the number of rows (see "The induction").

Provenance. Derived, internal; this is the elementary Gindikin–Karpelevich-type computation
described in `ComplexBlockChartIntegralStatement.md` ("Intended proof"). No literature statement
is claimed.

## Proof

### Leading principal submatrices (section `Leading`)

* `lead h A`: the leading `m × m` submatrix of an `a × a` matrix, for `h : m ≤ a`.
* `sum_eq_sum_castLE`: a sum over `Fin a` of a function vanishing on indices `≥ m` is a sum over
  `Fin m`. The proof uses `ComplexBlockChart.sum_castLE`.
* `lead_mul_mul_conjTranspose`: for lower triangular `T`, `lead(T S Tᴴ) = lead T · lead S · (lead T)ᴴ`.
* `lead_diagonal`, `isLowerTriangular_lead`, `det_lead_lower` and `det_lead_lower_ne_zero`.
* `vecMul_conjTranspose_castLE`: `(u Tᴴ)_i` for `i < m` only involves the first `m` coordinates
  of `u`.

### The rank-one identity (section `RankOne`)

* `rankOne u = uᴴ u`, the matrix `(conj(u_i) u_j)` (`rankOne_apply`, `rankOne_eq`).
* `mul_rankOne_mul`: `A (uᴴu) Aᴴ = (u Aᴴ)ᴴ (u Aᴴ)`.
* `det_diagonal_add_rankOne`: `det(diag(d) + vᴴ v) = det diag(d) · (1 + ∑ v_i d_i⁻¹ conj(v_i))`.
  This is the matrix determinant lemma `Matrix.det_add_replicateCol_mul_replicateRow`.
* `det_lead_add_rankOne`: suppose `T` is lower triangular and invertible with `T S Tᴴ = diag(d)`
  and all `d_i ≠ 0`. Then
  `det(S_m + u_mᴴ u_m) = det S_m · (1 + ∑_{i<m} (uTᴴ)_i d_i⁻¹ conj((uTᴴ)_i))`. To see this,
  conjugate by `T_m` and use the previous lemma for `D_m + v_mᴴ v_m`; then cancel
  `det T_m · det T_mᴴ ≠ 0`.

### The first row (section `Cons`)

* `gramS X' = 1 + X'ᴴ X'` is positive definite (`posDef_gramS`). `det_posDef_eq`: the
  determinant of a positive definite matrix is a positive real number (product of eigenvalues).
* `lead_gramS` and `colsUpTo_cons`:
  `1 + [x;X']_{≤l}ᴴ [x;X']_{≤l} = lead(gramS X') + rankOne(x_{≤l})`.
* LDL data from Mathlib (`Mathlib.Analysis.Matrix.LDL`):
  * `lowT X' = LDL.lowerInv`, lower triangular (`isLowerTriangular_lowT`) and invertible
    (`det_lowT_ne_zero`);
  * `diagD X' = LDL.diagEntries` with `lowT_conj : T S Tᴴ = diag(d)`;
  * `diagD_pos`, `diagD_eq`: the `d_i` are positive reals, as diagonal entries of the positive
    definite `T S Tᴴ`.
* `matM X' = Tᴴ · diag(d)^{-1/2}`. `norm_vecMul_matM_sq`: `|(xM)_i|² = |(xTᴴ)_i|² / d_i`.
* `colGram_cons`: `colGram [x;X'] l = colGram X' l · partialSq (x M) (l+1)`. This combines
  `det_lead_add_rankOne`, `term_eq`, and `sum_castLE_real` (the sum over `i ≤ l` as a
  `partialSq`).

### Rows and the factorization (section `Rows`)

* `rowGram_cons_succ`: `rowGram [x;X'] (j+1) = rowGram X' j`, by reindexing with `finCongr`.
* `rowGram_zero`: `rowGram X' 0 = Re det(gramS X')`, by Sylvester's identity
  `Matrix.det_one_add_mul_comm`. `gramS_zero`: for `k = 0`, `gramS = 1`.
* `rowPart` is the row factor of `blockChartBound`. `rowPart_cons`:
  `rowPart [x;X'] = (Re det gramS X')⁻¹ · rowPart X'`. `blockChartBound_eq` and
  `partialSq_nonneg` are used here.
* `blockChartBound_cons`:
  `blockChartBound ε [x;X'] = blockChartBound ε X' · (Re det S)⁻¹ · ∏_l partialSq(xM)(l+1)^{ε_l}`.
* `inv_norm_det_matM_sq`: `|det M|^{-2} = Re det S`. From `det(T S Tᴴ) = ∏ d_i` one gets
  `|det T|² det S = ∏ d_i`, while `|det M|² = |det T|² / ∏ d_i`.

### The induction (section `Integral`)

* Continuity: `continuous_colGram`, `continuous_rowGram`, `continuous_blockChartBound`.
* `constC ε` is the constant `C_ε`. `prod_partialSq_nonneg`, and `det_matM_ne_zero`.
* `lintegral_first_row`: `∫ ∏_l partialSq(xM)(l+1)^{ε_l} dx = Re det S · C_ε`. Proof:
  1. Change variables with `ComplexPartialJacquet.map_vecMulEquiv`; the Jacobian factor is
     `|det M|^{-2} = Re det S`.
  2. Under the tail condition, `ComplexPartialSqIntegral.integrable_prod_partialSq` shows that
     the remaining integral is the finite `C_ε` (`ofReal_integral_eq_lintegral_ofReal`).
* `lintegral_cons`: `∫ blockChartBound ε [x;X'] dx = blockChartBound ε X' · C_ε`, since `Re det S`
  cancels.
* `lintegral_eq_cons`: Tonelli for the first row, via `measurePreserving_piFinSuccAbove` and
  `lintegral_prod_symm'`.
* `blockChartBound_zero_rows`: with no rows the bound is `1`.
* `integrable_rows` (induction on `k`):
  * for `k = 0` the measure is finite (`Measure.pi_univ`) and the bound is constant;
  * for `k + 1`, the lower integral is `C_ε` times the lower integral for `k` rows, which is finite
    by the induction hypothesis (`hasFiniteIntegral_iff_ofReal`).
* `Langlands.Archimedean.complexBlockChartIntegrable : ComplexBlockChartIntegrableStatement`
  applies `integrable_rows`. The statement's hypothesis is
  `ComplexPartialSqIntegral.TailCondition ε 0`.

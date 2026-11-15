# Integrability of the block chart bound for `P_{a,k}` of `GL_{a+k}(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealBlockChartIntegralStatement`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
states one proposition and proves nothing. The proposition is the analytic input for the Langlands
lemma along the maximal parabolic subgroup `P_{a,k}` of `GL_{a+k}(ℝ)` when the last `k` exponents
are tied (equal real parts); see "Use" below. It is the real analogue of
`ComplexBlockChartIntegrableStatement` (module `ComplexBlockChartIntegralStatement`, Worker 140,
Task 7063).

## Definitions

All in the namespace `Langlands.Archimedean.RealBlockChart`; `X ∈ M_{k×a}(ℝ)` is a real `k × a`
matrix and `Xᵀ` its transpose.

* `colsUpTo X l` (for `l < a`): the `k × (l+1)` matrix `X_{≤l}` of the columns `0, …, l` of `X`.
* `rowsFrom X j` (for `j < k`): the `(k−j) × a` matrix `X^{(j)}` of the rows `j, …, k−1` of `X`.
* `colGram X l = det(1 + X_{≤l}ᵀ X_{≤l})` and `rowGram X j = det(1 + X^{(j)} X^{(j)ᵀ})`.
  The matrices are positive definite, so both numbers are at least `1`; this is not needed for the
  statement to make sense.
* `blockChartBound ε X = ∏_{l<a} colGram X l ^ ε_l · ∏_{j<k} (1 if j = 0, else rowGram X j ^ (−1/2))`,
  with real powers `^` (`Real.rpow`).

## The statement

`RealBlockChartIntegrableStatement`: for all `a, k ∈ ℕ` and `ε : Fin a → ℝ` with

`∑_{l ≥ j} (ε_l + 1/2) < 0` for every `j < a`

(written `∑_l (if j ≤ l then ε_l + 1/2 else 0) < 0`), the function `X ↦ blockChartBound ε X` is
integrable on `Fin k → Fin a → ℝ` (Lebesgue measure, the product of the Lebesgue measures of `ℝ`),
with `X` read as a matrix (`Matrix.of`).

Edge cases: for `k = 0` or `a = 0` the space `Fin k → Fin a → ℝ` is a single point of measure `1`
and the statement is trivially true. For `k = 1` the second product is empty and the statement is
the integrability of `x ↦ ∏_l (1 + ∑_{i ≤ l} x_i²)^{ε_l}` on `ℝ^a` under the cumulative condition
on the exponents. (The published `ParabolicChartBound` handles this function only through the
cruder bound `1 + ∑_{i ≤ l} x_i² ≥ 1 + x_l²`, which needs every `ε_l < −1/2`.)

Only sufficiency is stated; no converse is claimed. (For `k = 0` the condition is not necessary:
with `a = 1`, `k = 0`, `ε_0 = 0` the function is the constant `1` on a point, while the only tail
sum is `1/2`.)

## Provenance

Derived, internal; no literature source is claimed. It is the convergence of the Jacquet integral
over `N̄_{P_{a,k}}` of the spherical bound of a real principal series whose last `k` exponents are
tied, a special case of the Gindikin–Karpelevich convergence criterion for intertwining integrals.
For `n̄(X) = [[1, 0], [X, 1]]` the Gram determinant of the rows `≥ l` of `n̄(X)` is
`colGram X (l−1)` for `1 ≤ l ≤ a` and `rowGram X (l−a)` for `a ≤ l < a+k` (Schur complements).
A function `h` in the smooth principal series of `GL_n(ℝ)` with exponents `s_0, …, s_{n−1}` is
bounded on `n̄(X) O(n)` by a constant times the product of the Gram determinants of the rows `≥ l`
raised to `(σ_l − σ_{l−1})/2`, where `σ_l = Re s_l + (n−1)/2 − l`
(module `ParabolicChartBound`, `norm_le_chart` for `k = 1`); at a tied position
`Re s_{l−1} = Re s_l` the exponent is `−1/2`, which is the exponent of `rowGram X j` for
`j ≥ 1` above.

Intended proof (for a proof task): induction on `k`. Integrate row `0` of `X`, `x ∈ ℝ^a`. With
`X'` the remaining rows and `Q = 1 + X'ᵀX'`, the matrix determinant lemma
(Mathlib `Matrix.det_add_replicateCol_mul_replicateRow`) gives
`colGram X l = colGram X' l · (1 + x_{≤l} Q_{≤l}^{-1} x_{≤l}ᵀ)`, where `Q_{≤l}` is the top-left
`(l+1) × (l+1)` block of `Q`. With the LDL decomposition `Q = L D Lᵀ` (Mathlib `LDL.lower_conj_diag`, with `ᴴ = ᵀ` over `ℝ`,
`L` lower unitriangular) and `z_i = (x (Lᵀ)^{-1})_i / √d_i`, one has
`x_{≤l} Q_{≤l}^{-1} x_{≤l}ᵀ = ∑_{i ≤ l} z_i²` and `dx = (det Q)^{1/2} dz`, so the inner integral is
`(det Q)^{1/2} ∏_l colGram X' l ^ ε_l · ∫_{ℝ^a} ∏_l (1 + ∑_{i≤l} z_i²)^{ε_l} dz`. The last integral
is finite under the cumulative condition (integrate the coordinates from the last one with
`∫_ℝ (A + t²)^γ dt = c_γ A^{γ+1/2}` for `γ < −1/2`). Since
`det Q = det(1 + X'X'ᵀ) = rowGram X 1` (Weinstein–Aronszajn, `Matrix.det_one_add_mul_comm`) and
`rowGram X (j+1) = rowGram X' j`, the factor `(det Q)^{1/2}` cancels `rowGram X 1 ^ (−1/2)`, and the
remaining integrand is a constant times `blockChartBound ε X'`. Tonelli concludes.

## Use

In Task 6749, ties of the Langlands order among character blocks are handled by the Langlands lemma
along `P_{a,k}` with the last block of `k` tied exponents: this statement gives the convergence of
the partial Jacquet integral `∫ h(n̄(X) g) dX` over `N̄_{P_{a,k}}` and the dominating function for
the limit argument (where the exponents `ε_l` become `max(ε_l, −1)`).

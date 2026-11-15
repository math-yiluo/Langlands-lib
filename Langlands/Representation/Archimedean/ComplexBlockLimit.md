# The limit argument along the maximal parabolic subgroup `P_{a,k+1}` of `GL_{a+k+1}(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexBlockLimit`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It generalizes the published limit argument
`ComplexJacquetLimit` (along `P_{m,1}`, strictly decreasing exponents) to the maximal parabolic
subgroup `P_{a,k+1}` whose last block of size `k+1` carries exponents with equal real parts. This
is the step needed for Langlands-ordered lists with ties.

Notation: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ` and `U(N)` is `unitaryCompact ℂ N`, with the
Haar probability measure `ComplexDuality.unitaryHaar N`. `n̄(X) = [[1, 0], [X, 1]]`
(`blockLowerGL`) and `diag(κ₁, κ₂)` (`blockDiagGL`) come from
`ComplexBlockParabolicIntegrationStatement`. `colGram`, `rowGram` and
`blockChartBound ε X = ∏_{l<a} colGram X l ^ ε_l · ∏_{1≤j≤k} (rowGram X j)⁻¹` come from
`ComplexBlockChartIntegralStatement`, and `norm_le_blockChartBound` from
`ComplexBlockChartBound`. `IsPhasePower χ e` (`ComplexPartialJacquet`) means
`χ_l(z) = χ_l(z/|z|)(|z|²)^{e_l}`, `χ_l(1) = 1` and `|χ_l| = 1` on the unit circle. `dualChar χ`
is `l, z ↦ (χ_l z)⁻¹`. Unprefixed names below are in the namespace
`Langlands.Archimedean.ComplexBlockLimit`.

## The statement

`ComplexBlockLimitStatement` is an implication. It assumes the two statements
`ComplexBlockChartIntegrableStatement` (integrability of `blockChartBound` under a tail
condition) and `ComplexBlockParabolicIntegrationStatement` (the `U(a+k)`-integral in coordinates of
`P_{a,k}`). These are only stated, not yet proved, in the Library. Under these assumptions it says:

Let `a, k ∈ ℕ` and let `χ` be phase-power characters with exponents `e` such that

* `Re e_{l+1} ≤ Re e_l` for `l < a`,
* `Re e_a < Re e_{a−1}` (when `a ≥ 1`), and
* `Re e_a = Re e_{a+1} = ⋯ = Re e_{a+k}`.

Let `u` be in `principalSeries ℂ (a+k+1) (fun l z => (χ l z)⁻¹)` and `h` in
`principalSeries ℂ (a+k+1) χ`. Suppose `∫_{U(a+k+1)} u(κ g) h(κ) dκ = 0` for every
`g ∈ GL_{a+k+1}(ℂ)`. Then

`∫_{U(a)} ∫_{U(k+1)} u(diag(κ₁, κ₂)) (∫_{M_{(k+1)×a}(ℂ)} h(n̄(X) diag(κ₁, κ₂)) dX) dκ₂ dκ₁ = 0`

(Lebesgue measure on `M_{(k+1)×a}(ℂ) = Fin (k+1) → Fin a → ℂ`). It is proved as
`Langlands.Archimedean.complexBlockLimit`, from
`ComplexBlockLimit.integral_mul_blockStep_eq_zero`.

For `k = 0`, `n̄(X)` is the matrix `J(x, 1)` of `ComplexJacquetLimitStatement` (identity with last
row `(x, 1)`), and the statement is an analogue of that one with an additional integral over
`κ₂ ∈ U(1)`. Its order hypothesis is weaker: decreasing real parts, strict only at the last step,
instead of strictly decreasing.

Provenance. Derived. This is the standard leading-term (Langlands lemma) argument along a maximal
parabolic subgroup, internal infrastructure for the Langlands quotient. It mirrors the published
`ComplexJacquetLimit` and makes no claim beyond the Lean statement.

## Proof

### Determinants of `1 + cA` for positive semidefinite `A` (section `Det`)

* `det_one_add_smul_eq_prod`: if `A` is Hermitian positive semidefinite with eigenvalues `λ_i`, then
  `det(1 + cA) = ∏ (1 + c λ_i)` for real `c` (spectral theorem `IsHermitian.spectral_theorem`).
* `re_det_one_add_smul` is its real part. `one_le_re_det` gives `1 ≤ Re det(1 + cA)` for `c ≥ 0`,
  and `re_det_mono` says `c ↦ Re det(1 + cA)` is monotone on `c ≥ 0`.

### Scaling the block chart (section `Scaling`)

* `colGram_smul`, `rowGram_smul`: `colGram (tX) l = Re det(1 + t² X_{≤l}ᴴ X_{≤l})` and
  `rowGram (tX) j = Re det(1 + t² X^{(j)} X^{(j)ᴴ})` for real `t`. `colGram_eq` and `rowGram_eq` are
  the case `t = 1`.
* `one_le_colGram`, `one_le_rowGram`: both are `≥ 1`. `colGram_smul_le` and `rowGram_smul_le`:
  both decrease when `X` is replaced by `tX` with `|t| ≤ 1`. `blockChartBound_nonneg`.
* `blockChartBound_mul_le` (domination): if `ε^u_l + ε^h_l = −2` for all `l` and `|t| ≤ 1`, then
  `blockChartBound ε^u (tX) · blockChartBound ε^h X ≤ blockChartBound (max(ε^h, −2)) X`. Proof,
  factor by factor:
  * for `l` with `ε^u_l ≥ 0`, `G(tX)^{ε^u} G(X)^{ε^h} ≤ G(X)^{−2} ≤ G(X)^{max(ε^h,−2)}`;
  * otherwise `G(tX)^{ε^u} ≤ 1`, so the factor is at most `G(X)^{ε^h} ≤ G(X)^{max(ε^h,−2)}`, because
    every Gram factor `G` is `≥ 1`;
  * the row factors satisfy `rowGram(tX)⁻¹ ≤ 1`.

### The central element `d(s) = diag(1_a, s·1_{k+1})` (section `Central`)

* `tailMat s = diag(1_a, s·1_k)` and `dTail s = Iwasawa.diagonalUnits (tailEntries s)`, the
  diagonal matrix with entries `1` before position `a` and `s` after it. `dTail_val` says its matrix
  is `tailMat s`.
* `blockLowerGL_mul_dTail`: `n̄(X) d(s) = d(s) n̄(s⁻¹X)` (`blockLower_mul_blockDiag_tail`, block
  multiplication via `reindex_mul_reindex`).
* `blockDiagGL_mul_dTail`: `d(s)` commutes with `diag(g₁, g₂)` (`blockDiag_mul_blockDiag_tail`).
  `blockDiagGL_val` gives the matrix of `blockDiagGL`.
* Continuity: `continuous_blockLower`, `continuous_blockLowerGL` (the inverse of `n̄(X)` is
  `n̄(−X)`, `blockLower_mul_blockLower_neg`) and `continuous_blockDiagGL`. Also
  `blockLowerGL_zero : n̄(0) = 1`.

### Bounds (section `Bounds`)

* `norm_le_block`: for `h` in the principal series of phase-power characters with
  `Re e_{a+j} = Re e_a` (`j ≤ k`) and `‖h‖ ≤ C` on `U(a+k+1)`,
  `‖h(n̄(X) κ)‖ ≤ C · blockChartBound (l ↦ Re e_{l+1} − Re e_l − 1) X` for unitary `κ`. This is
  `ComplexBlockChart.norm_le_blockChartBound` with `σ_l = 2(Re e_l + (N−1)/2 − l)`,
  `N = a+k+1`, using `ComplexPartialJacquet.norm_principalSeriesCharacter`. The ties give the
  condition `(σ_{a+j} − σ_{a+j−1})/2 = −1`.
* `blockDiagGL_mem_unitaryCompact`: `diag(κ₁, κ₂)` is unitary for unitary `κ₁, κ₂`.
* `tail_max`: the hypotheses `Re e_{l+1} ≤ Re e_l` (`l < a`) and `Re e_a < Re e_{a−1}` imply the
  tail condition of `ComplexBlockChartIntegrableStatement` for the exponents
  `γ_l = max(Re e_{l+1} − Re e_l − 1, −2)`. These satisfy `γ_l ≤ −1` and `γ_{a−1} < −1`, so
  `ComplexPartialSqIntegral.tailCondition_of_le` applies.

### The pairing identity (section `Pairing`)

`Φ u h s κ₁ κ₂ X = u(n̄(s⁻¹X) diag(κ₁, κ₂)) · h(n̄(X) diag(κ₁, κ₂))`.

`integral_Φ_eq_zero`: for `s > 0`, `∫_{U(a)} ∫_{U(k+1)} ∫_X Φ_s = 0`. Proof:

1. Let `d = d(s)`. The function `F(y) = u(y d) h(y)` lies in the principal series of the modulus
   character (`rightTranslation_mem_principalSeries`,
   `ComplexJacquetLimit.principalSeriesCharacter_dual_mul`).
2. Hence `∫_{U} F = c ∫∫∫ F(n̄(X) diag(κ₁, κ₂))` with `c > 0`, by
   `ComplexBlockParabolicIntegrationStatement`. The left side is `0` by the hypothesis with `g = d`.
3. By the two commutation rules, `F(n̄(X) diag(κ₁, κ₂)) = u(d · n̄(s⁻¹X) diag(κ₁, κ₂)) h(…)`, and
   `u(d y) = c' u(y)` with `c' = principalSeriesCharacter (dualChar χ) (tailEntries s) ≠ 0`.
4. So `0 = c c' ∫∫∫ Φ_s`.

### Domination and the limit (section `Limit`)

* `secondCountableTopology_unitaryCompact` (instance): `U(n)` is second countable. Its topology
  is induced from `M_n(ℂ) × M_n(ℂ)ᵐᵒᵖ` through `Units.embedProduct`. This instance is used for
  measurability on products of unitary groups.
* `continuous_Φ`: `t ↦ Φ_s(f₁ t, f₂ t, f_X t)` is continuous for continuous `f₁, f₂, f_X`.
* `norm_Φ_le`: for `s ≥ 1`, `‖Φ_s(κ₁, κ₂, X)‖ ≤ C_u C_h blockChartBound γ X` with `γ` as above.
  This combines `norm_le_block` for `u` (exponents `−e`, via `IsPhasePower.dual`) and for `h` with
  `blockChartBound_mul_le` (`t = s⁻¹`, `ε^u_l + ε^h_l = −2`).
* `integral_mul_blockStep_eq_zero`: the dominating function `C_u C_h blockChartBound γ` is
  integrable by `ComplexBlockChartIntegrableStatement` and `tail_max`. Along `s = n + 1`,
  dominated convergence is applied three times:
  * the `X`-integral, pointwise, by continuity of `u` and `n̄(s⁻¹X) → n̄(0) = 1`;
  * the `κ₂`-integral, with the constant bound `∫ D`;
  * the `κ₁`-integral, with the same constant bound.

  The required measurability comes from `AEStronglyMeasurable.integral_prod_right'` and
  `continuous_Φ`. The limit is
  `∫∫ u(diag(κ₁, κ₂)) ∫ h(n̄(X) diag(κ₁, κ₂)) dX`, and every term of the sequence is `0` by
  `integral_Φ_eq_zero`.

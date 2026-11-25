# The limit argument along the maximal parabolic subgroup `P_{a,k+1}` of `GL_{a+k+1}(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealBlockLimit`.

This module was written for the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
generalizes the published limit argument `JacquetLimit` (along `P_{m,1}`, strictly decreasing
exponents) to the maximal parabolic subgroup `P_{a,k+1}` whose last block of size `k+1` carries
exponents with equal real parts; this is the step needed for Langlands-ordered character lists
with ties. The module is the real analogue of `ComplexBlockLimit` and
follows its structure.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is `unitaryCompact ℝ N`, with the
Haar probability measure `RealPrincipalSeriesDuality.haarK N`. `n̄(X) = [[1, 0], [X, 1]]`
(`blockLowerGL`), `blockLower`, `diag(κ₁, κ₂)` (`blockDiagGL`) and the matrix
`RealBlockParabolic.blockDiag` come from `RealBlockParabolicIntegrationStatement`. `colGram`,
`rowGram`, `colsUpTo`, `rowsFrom` and
`blockChartBound ε X = ∏_{l<a} colGram X l ^ ε_l · ∏_{1≤j≤k} rowGram X j ^ (−1/2)` come from
`RealBlockChartIntegralStatement`, and `RealBlockChart.norm_le_blockChartBound` from
`RealBlockChartBound`. `IsSignedPower χ e` (module `PartialJacquetIntegral`) means
`χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and `‖χ_l(−1)‖ = 1`; `dualChar χ` is
`l, x ↦ (χ_l x)⁻¹`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.RealBlockLimit`.

## The statement

`RealBlockLimitStatement` is an implication. It assumes the two statements
`RealBlockChartIntegrableStatement` (integrability of `blockChartBound` when every tail sum of
`ε_l + 1/2` is negative) and `RealBlockParabolicIntegrationStatement` (the `O(a+k)`-integral in
coordinates of `P_{a,k}`). The Library proves them as `realBlockChartIntegrable` (`RealBlockChartIntegralProof`) and
`realBlockParabolicIntegration` (`RealBlockParabolicIntegrationProof`). Under these
assumptions it says:

Let `a, k ∈ ℕ` and let `χ_0, χ_1, …` be characters of `ℝˣ` with
`χ_l(x) = χ_l(sgn x) |x|^{e_l}` (`GramFormula.signUnit x` is the sign of `x`), `χ_l(1) = 1` and
`‖χ_l(−1)‖ = 1`, such that

* `Re e_{l+1} ≤ Re e_l` for `l < a`,
* `Re e_a < Re e_{a−1}` (a condition only when `a ≥ 1`), and
* `Re e_a = Re e_{a+1} = ⋯ = Re e_{a+k}`.

Let `u` be in `principalSeries ℝ (a+(k+1)) (fun l x => (χ l x)⁻¹)` and `h` in
`principalSeries ℝ (a+(k+1)) χ`. Suppose `∫_{O(a+k+1)} u(κ g) h(κ) dκ = 0` for every
`g ∈ GL_{a+k+1}(ℝ)`. Then

`∫_{O(a)} ∫_{O(k+1)} u(diag(κ₁, κ₂)) (∫_{M_{(k+1)×a}(ℝ)} h(n̄(X) diag(κ₁, κ₂)) dX) dκ₂ dκ₁ = 0`

(Lebesgue measure on `M_{(k+1)×a}(ℝ) = Fin (k+1) → Fin a → ℝ`, Haar probability measures on
`O(a)` and `O(k+1)`). It is proved as `Langlands.Archimedean.realBlockLimit`, from
`RealBlockLimit.integral_mul_blockStep_eq_zero`.

For `k = 0` the matrix `n̄(X)` is the matrix `J(x, 1)` of `JacquetLimit` (the identity with last
row `(x, 1)`), and the statement is an analogue of `JacquetLimit.integral_mul_jacquetStep_eq_zero`
with an additional integral over `κ₂ ∈ O(1)`. Its order hypothesis is weaker: decreasing real
parts, strict only at the last step, instead of strictly decreasing.

Provenance. Derived. This is the standard leading-term (Langlands lemma) argument along a maximal
parabolic subgroup, internal infrastructure for the Langlands quotient. It mirrors the published
`JacquetLimit` and `ComplexBlockLimit`, and makes no claim beyond the Lean statement.

## Proof

### Determinants of `1 + cA` for positive semidefinite `A` (section `Det`)

* `det_one_add_smul_eq_prod`: if the real matrix `A` is positive semidefinite with eigenvalues
  `λ_i`, then `det(1 + cA) = ∏ (1 + c λ_i)` for real `c` (spectral theorem
  `IsHermitian.spectral_theorem`).
* `one_le_det`: `1 ≤ det(1 + cA)` for `c ≥ 0`; `det_mono`: `c ↦ det(1 + cA)` is monotone on
  `c ≥ 0`.
* `posSemidef_transpose_mul_self`, `posSemidef_self_mul_transpose`: `MᵀM` and `MMᵀ` are positive
  semidefinite.

### Scaling the block chart (section `Scaling`)

* `colGram_smul`, `rowGram_smul`: `colGram (tX) l = det(1 + t² X_{≤l}ᵀ X_{≤l})` and
  `rowGram (tX) j = det(1 + t² X^{(j)} X^{(j)ᵀ})` for real `t`; `colGram_eq` and `rowGram_eq` are
  the case `t = 1`.
* `one_le_colGram`, `one_le_rowGram`: both are `≥ 1`. `colGram_smul_le` and `rowGram_smul_le`:
  both decrease when `X` is replaced by `tX` with `|t| ≤ 1`. `blockChartBound_nonneg`.
* `blockChartBound_mul_le` (domination): if `ε^u_l + ε^h_l = −1` for all `l` and `|t| ≤ 1`, then
  `blockChartBound ε^u (tX) · blockChartBound ε^h X ≤ blockChartBound (max(ε^h, −1)) X`. Proof,
  factor by factor, using that every Gram factor `G` is `≥ 1`:
  * for `l` with `ε^u_l ≥ 0`, `G(tX)^{ε^u_l} G(X)^{ε^h_l} ≤ G(X)^{−1} ≤ G(X)^{max(ε^h_l,−1)}`;
  * otherwise `G(tX)^{ε^u_l} ≤ 1`, so the factor is at most
    `G(X)^{ε^h_l} ≤ G(X)^{max(ε^h_l,−1)}`;
  * the row factors satisfy `rowGram(tX) j ^ (−1/2) ≤ 1`.

### The central element `d(s) = diag(1_a, s·1_k)` (section `Central`)

* `tailMat s = diag(1_a, s·1_k)` and `dTail s = Iwasawa.diagonalUnits (tailEntries s)`, the
  diagonal matrix with entries `1` before position `a` and `s` from position `a` on. `dTail_val`
  says its matrix is `tailMat s`.
* `blockLowerGL_mul_dTail`: `n̄(X) d(s) = d(s) n̄(s⁻¹X)` (`blockLower_mul_blockDiag_tail`, block
  multiplication via `reindex_mul_reindex`).
* `blockDiagGL_mul_dTail`: `d(s)` commutes with `diag(g₁, g₂)` (`blockDiag_mul_blockDiag_tail`).
  `blockDiagGL_val` gives the matrix of `blockDiagGL`.
* Continuity: `continuous_blockLower`, `continuous_blockLowerGL` (the inverse of `n̄(X)` is
  `n̄(−X)`, `blockLower_mul_blockLower_neg`) and `continuous_blockDiagGL`. Also
  `blockLowerGL_zero : n̄(0) = 1`.

### Bounds (section `Bounds`)

* `norm_le_block`: for `h` in the principal series of signed-power characters with
  `Re e_{a+j} = Re e_a` (`j ≤ k`) and `‖h‖ ≤ C` on `O(a+k+1)`,
  `‖h(n̄(X) κ)‖ ≤ C · blockChartBound (l ↦ (Re e_{l+1} − Re e_l − 1)/2) X` for orthogonal `κ`.
  This is `RealBlockChart.norm_le_blockChartBound` with
  `σ_l = PartialJacquet.normExponent e N l = Re e_l + (N−1)/2 − l`, `N = a+k+1`, using
  `PartialJacquet.norm_principalSeriesCharacter`. The ties give the hypothesis
  `(σ_{a+j} − σ_{a+j−1})/2 = −1/2` for `1 ≤ j ≤ k`.
* `blockDiagGL_mem_unitaryCompact`: `diag(κ₁, κ₂)` is orthogonal for orthogonal `κ₁, κ₂`.
* `tail_max`: the hypotheses `Re e_{l+1} ≤ Re e_l` (`l < a`) and `Re e_a < Re e_{a−1}` imply the
  tail condition `∑_{l ≥ j} (γ_l + 1/2) < 0` of `RealBlockChartIntegrableStatement` for the
  exponents `γ_l = max((Re e_{l+1} − Re e_l − 1)/2, −1)`: every summand is `≤ 0` because
  `γ_l ≤ −1/2`, and the summand `l = a−1` (present in every tail) is `< 0` because
  `γ_{a−1} < −1/2`.

### The pairing identity (section `Pairing`)

`Φ u h s κ₁ κ₂ X = u(n̄(s⁻¹X) diag(κ₁, κ₂)) · h(n̄(X) diag(κ₁, κ₂))`.

`integral_Φ_eq_zero`: for `s > 0`, `∫_{O(a)} ∫_{O(k+1)} ∫_X Φ_s = 0`. Proof:

1. Let `d = d(s)`. The function `F(y) = u(y d) h(y)` is smooth
   (`RealPrincipalSeriesDuality.contMDiff_mul_fun`; `u(· d)` is in the principal series by
   `rightTranslation_mem_principalSeries`) and modulus covariant
   (`MaximalParabolicIntegration.IsModulusCovariant`, by
   `JacquetLimit.principalSeriesCharacter_dual_mul`).
2. Hence `∫_{O(a+k+1)} F = c ∫∫∫ F(n̄(X) diag(κ₁, κ₂))` with `c > 0`, by
   `RealBlockParabolicIntegrationStatement`. The left side is `0` by the hypothesis with `g = d`.
3. By the two commutation rules, `F(n̄(X) diag(κ₁, κ₂)) = u(d · n̄(s⁻¹X) diag(κ₁, κ₂)) h(…)`, and
   `u(d y) = c' u(y)` with `c' = principalSeriesCharacter (dualChar χ) (tailEntries s) ≠ 0`.
4. So `0 = c c' ∫∫∫ Φ_s`, and `c c' ≠ 0`.

### Domination and the limit (section `Limit`)

* `secondCountableTopology_unitaryCompact` (local instance): `O(n)` is second countable; its
  topology is induced from `M_n(ℝ) × M_n(ℝ)ᵐᵒᵖ` through `Units.embedProduct`. The local instance
  `borelSpaceK_bl` says that the measurable structure `measurableSpaceK` is the Borel one. They
  are used for measurability on products of orthogonal groups.
* `continuous_Φ`: `t ↦ Φ_s(f₁ t, f₂ t, f_X t)` is continuous for continuous `f₁, f₂, f_X`.
* `norm_Φ_le`: for `s ≥ 1`, `‖Φ_s(κ₁, κ₂, X)‖ ≤ C_u C_h blockChartBound γ X` with `γ` as above.
  This combines `norm_le_block` for `u` (exponents `−e`, via `IsSignedPower.dual`) and for `h`
  with `blockChartBound_mul_le` (`t = s⁻¹`, `ε^u_l + ε^h_l = −1`).
* `integral_mul_blockStep_eq_zero`: the dominating function `D = C_u C_h blockChartBound γ` is
  integrable by `RealBlockChartIntegrableStatement` and `tail_max` (`C_u`, `C_h` bound `u`, `h` on
  `O(a+k+1)`, `PartialJacquet.exists_bound_unitaryCompact`). Along `s = n + 1`, dominated
  convergence is applied three times:
  * the `X`-integral, pointwise in `(κ₁, κ₂)`, with dominating function `D`, by continuity of `u`
    and `n̄(s⁻¹X) → n̄(0) = 1`;
  * the `κ₂`-integral, with the constant bound `∫ D`;
  * the `κ₁`-integral, with the same constant bound.

  The required measurability comes from `AEStronglyMeasurable.integral_prod_right'` and
  `continuous_Φ`. The limit is
  `∫∫ u(diag(κ₁, κ₂)) ∫ h(n̄(X) diag(κ₁, κ₂)) dX`, and every term of the sequence is `0` by
  `integral_Φ_eq_zero`.

# The partial Jacquet integral along the maximal parabolic subgroup `P_{a,k+1}` of `GL_{a+k+1}(ℝ)`

Lean module: `Langlands.Representation.Archimedean.RealBlockJacquet`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
generalizes the published `PartialJacquetIntegral` (`P_{m,1}`, strictly decreasing exponents) to
the maximal parabolic subgroup `P_{a,k+1}` whose last block of size `k+1` carries exponents with
equal real parts. The function `h'` defined here is the input of the next step of the
Langlands-quotient recursion on `GL_a(ℝ)`. The module is the real analogue of Worker 140's
`ComplexBlockJacquet` (Task 7063) and follows its structure.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and `O(N)` is `unitaryCompact ℝ N`, with the
Haar probability measure `RealPrincipalSeriesDuality.haarK N`. `n̄(X) = [[1, 0], [X, 1]]`
(`blockLowerGL`), `blockLower`, `diag(g₁, g₂)` (`blockDiagGL`) and the matrix
`RealBlockParabolic.blockDiag` come from `RealBlockParabolicIntegrationStatement`.
`blockChartBound` comes from `RealBlockChartIntegralStatement`, and `RealBlockLimit.norm_le_block`,
`RealBlockLimit.continuous_blockLowerGL`, `RealBlockLimit.continuous_blockDiagGL` and
`RealBlockLimit.blockDiagGL_mem_unitaryCompact` from `RealBlockLimit`. `IsSignedPower χ e`
(module `PartialJacquetIntegral`) means `χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and
`‖χ_l(−1)‖ = 1`; `GramFormula.signUnit x` is the sign of `x`. `kFiniteFunctions`,
`principalSeries`, `principalSeriesCharacter`, `Iwasawa.diagonalUnits` and `upperUnipotent` are
the Library's. Unprefixed names below are in the namespace
`Langlands.Archimedean.RealBlockJacquet`.

## Definitions

* `blockShiftChar k χ l x = χ_l(x) |x|^{-(k+1)/2}`: the characters of `GL_a(ℝ)` attached to the
  first `a` positions.
* `IsBlockDominant e a k`: `Re e_{a+j} = Re e_a` for `j ≤ k` (`tie`), `Re e_{l+1} ≤ Re e_l` for
  `l < a` (`ord`) and `Re e_{l+1} < Re e_l` for `l + 1 = a` (`gap`).
* `blockStep h g = ∫_{M_{(k+1)×a}(ℝ)} h(n̄(X) g) dX` (the partial Jacquet integral `T_P h`;
  Lebesgue measure on `Fin (k+1) → Fin a → ℝ`, `X` read as a matrix by `Matrix.of`).
* `blockPair φ h g₁ = ∫_{O(k+1)} φ(κ₂) · blockStep h (diag(g₁, κ₂)) dκ₂` for
  `φ : GL_{k+1}(ℝ) → ℂ` and `g₁ ∈ GL_a(ℝ)`.

## The statement

`RealBlockJacquetStatement` assumes `RealBlockChartIntegrableStatement`, which is only stated, not
yet proved, in the Library. Under that assumption it says the following.

Let `a, k ∈ ℕ` and let `χ_0, χ_1, …` be characters of `ℝˣ` with
`χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and `‖χ_l(−1)‖ = 1`, such that

* `Re e_{l+1} ≤ Re e_l` for `l < a`,
* `Re e_a < Re e_{a−1}` (a condition only when `a ≥ 1`), and
* `Re e_a = Re e_{a+1} = ⋯ = Re e_{a+k}`,

given as separate hypotheses. For every `O(a+k+1)`-finite function `h` of
`principalSeries ℝ (a+k+1) χ`:

1. `X ↦ h(n̄(X) κ)` is integrable on `M_{(k+1)×a}(ℝ)` for every `κ ∈ O(a+k+1)`;
2. for every continuous `φ` on `GL_{k+1}(ℝ)`, `blockPair φ h` is an `O(a)`-finite function of
   `principalSeries ℝ a (blockShiftChar k χ)`.

It is proved as `Langlands.Archimedean.realBlockJacquet`, from `integrable_block` and
`blockPair_mem`.

Provenance. Derived, internal infrastructure: the standard partial Jacquet (intertwining) integral
along a maximal parabolic subgroup, here with a tied last block. It mirrors the published
`PartialJacquetIntegral` and makes no claim beyond the Lean statement.

## Proof

### Change of variables (section `RowMul`)

* `det_vecMulLinearEquiv`: the map `x ↦ x B` on `ℝ^a` (`PartialJacquet.vecMulLinearEquiv`) is
  `Matrix.toLin' Bᵀ`, so its determinant is `det B`.
* `rowMulLinearEquiv`: `X ↦ X B`, row by row (`LinearEquiv.piCongrRight`).
  `det_rowMulLinearEquiv`: its determinant is `(det B)^{k+1}`, by `LinearMap.det_pi`.
* `isAddHaarMeasure_volume_rows` (instance): Lebesgue measure on `Fin (k+1) → Fin a → ℝ` is an
  additive Haar measure.
* `rowMulEquiv`, `map_rowMulEquiv`: Lebesgue measure is mapped to `|(det B)^{k+1}|^{-1}` times
  itself (`Measure.map_linearMap_addHaar_eq_smul_addHaar`).
* `integral_rowMul_eq`: `∫ f(X B) dX = (|det B|^{k+1})^{-1} ∫ f`.

### Block matrices (section `Group`)

* `blockDiagGL_mul`: `diag(g₁, g₂) diag(g₁', g₂') = diag(g₁g₁', g₂g₂')`.
* `blockDiagGL_diagonalUnits`: `diag(diag(z), 1) = diag(z, 1, …, 1)` (`Fin.addCases`).
* `blockDiagGL_mem_upperUnipotent`: `diag(u, 1)` is upper unipotent for upper unipotent `u`.
* `blockLower_mul_blockDiag_one`, `blockLowerGL_mul_blockDiagGL`:
  `n̄(X) diag(g, 1) = diag(g, 1) n̄(X g)`.

### Characters (section `Shift`)

* `isSignedPower_blockShift`: `blockShiftChar k χ` is signed-power with exponents
  `e_l − (k+1)/2`.
* `cpow_combine`: an exponent bookkeeping identity `c x^{s₁} (x^n)^{-1} = c x^t x^{s₂}` when
  `s₁ − n = t + s₂`.
* `principalSeriesCharacter_addCases`: if `χ_j(1) = 1` for `j ≥ a`, then
  `principalSeriesCharacter (a+k+1) χ (z, 1, …, 1) · ((∏_i |z_i|)^{k+1})^{-1} =
  principalSeriesCharacter a (blockShiftChar k χ) z`. Factor by factor, the exponents
  `(a+k)/2 − i − (k+1)` and `−(k+1)/2 + (a−1)/2 − i` of `|z_i|` agree.

### Equivariance (section `Step`)

`blockStep_mul`: for `b = diag(z) u` in the Borel subgroup of `GL_a(ℝ)`,
`T_P h(diag(b g₁, g₂)) = principalSeriesCharacter a (blockShiftChar k χ) z · T_P h(diag(g₁, g₂))`.
Proof:

1. Write `diag(b g₁, g₂) = diag(b, 1) diag(g₁, g₂)` and `n̄(X) diag(b, 1) = diag(b, 1) n̄(X b)`
   (`of_mul_eq_of_vecMul`). Here `diag(b, 1) = diag(z, 1, …, 1) · diag(u, 1)` with an upper
   unipotent second factor.
2. The principal-series property of `h` gives the factor
   `principalSeriesCharacter (a+k+1) χ (z, 1, …, 1)`.
3. The substitution `X ↦ X b` (`integral_rowMul_eq`, `det b = ∏ z_i`, using
   `MaximalParabolicIntegration.det_upperUnipotent`) gives `((∏ |z_i|)^{k+1})^{-1}`.
4. These two factors combine by `principalSeriesCharacter_addCases`.

### Integrability, continuity and finiteness (section `Pair`)

* `tail_h`: `IsBlockDominant` implies the tail condition of `RealBlockChartIntegrableStatement` for
  the exponents `ε_l = (Re e_{l+1} − Re e_l − 1)/2`: each `ε_l + 1/2 = (Re e_{l+1} − Re e_l)/2` is
  `≤ 0` by `ord`, and `< 0` at `l = a − 1` by `gap`, so every tail sum is negative
  (`Finset.sum_lt_sum`).
* `integrable_block`: `h(n̄(X) κ)` is dominated by `C · blockChartBound ε X`
  (`RealBlockLimit.norm_le_block`, with `C` a bound for `|h|` on `O(a+k+1)` from
  `PartialJacquet.exists_bound_unitaryCompact`), which is integrable by the assumed statement.
* `continuous_blockStep`: `t ↦ T_P h(diag(f₁ t, f₂ t))` is continuous for continuous maps `f₁, f₂`
  into the orthogonal groups on a first-countable space (`continuous_of_dominated`, same
  dominating function). `norm_blockStep_le` bounds `T_P h` on `O(a+k+1)` by
  `∫ C · blockChartBound ε`.
* `blockPair_mul`: `blockPair φ h (diag(z) u g₁) = principalSeriesCharacter a (blockShiftChar k χ) z ·
  blockPair φ h g₁`, from `blockStep_mul`.
* `continuous_blockPair`: `κ ↦ blockPair φ h κ` is continuous on the matrix orthogonal group, by
  dominated convergence with a constant bound (`Cφ · ∫ C · blockChartBound ε`, with `Cφ` a bound
  of `|φ|` on `O(k+1)`).
* `blockPairOn`: `f ↦ (κ ↦ blockPair φ f κ)` is linear on any submodule of the principal series.
  The `X`- and `κ₂`-integrals are additive by `integrable_block` and
  `RealPrincipalSeriesDuality.integrable_of_continuous` (continuous functions on `O(n)` are
  `haarK`-integrable).
* `blockPair_rightTranslation`: right translation of `f` by `diag(κ, 1)` becomes right translation
  of `blockPair φ f` by `κ`.
* `finiteDimensional_blockPair`: the right `O(a)`-translates of `κ ↦ blockPair φ h κ` lie in the
  image under `blockPairOn` of the finite-dimensional span of the `O(a+k+1)`-translates of `h`
  (these lie in the principal series by `rightTranslation_mem_principalSeries`).
* `blockPair_mem`: the function `ψ(κ) = blockPair φ h κ` on `O(a)` satisfies the hypotheses of
  `PrincipalSeriesExtension.extension_mem_kFiniteFunctions` for the signed-power characters
  `blockShiftChar k χ`: continuity, finiteness, and equivariance under the sign matrices
  `PrincipalSeriesExtension.signDiagonal d` (via `PartialJacquet.signDiagonal_toUnits` and
  `blockPair_mul`). The resulting extension agrees with `blockPair φ h` on `diag(z) u κ`
  (Iwasawa decomposition, `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact` from
  `RealStandardModuleAdmissible`), because both sides satisfy the same equivariance and agree on
  `O(a)` (`PrincipalSeriesExtension.extension_unitary`).

The section `Pair` uses `RealBlockLimit.secondCountableTopology_unitaryCompact` and a local
`BorelSpace` instance on `O(n)` for the dominated-convergence and integrability lemmas.

# The partial Jacquet integral along the maximal parabolic subgroup `P_{a,k+1}` of `GL_{a+k+1}(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexBlockJacquet`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It generalizes the published `ComplexPartialJacquet`
(`P_{m,1}`, strictly decreasing exponents) to the maximal parabolic subgroup `P_{a,k+1}` whose last
block of size `k+1` carries exponents with equal real parts. The function `h'` defined here is the
input of the next step of the Langlands-quotient recursion on `GL_a(ℂ)`.

Notation: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ` and `U(N)` is `unitaryCompact ℂ N`, with the
Haar probability measure `ComplexDuality.unitaryHaar N`. `n̄(X) = [[1, 0], [X, 1]]`
(`blockLowerGL`) and `diag(g₁, g₂)` (`blockDiagGL`) come from
`ComplexBlockParabolicIntegrationStatement`. `blockChartBound` comes from
`ComplexBlockChartIntegralStatement`. `IsPhasePower χ e` (`ComplexPartialJacquet`) means
`χ_l(z) = χ_l(z/|z|)(|z|²)^{e_l}`, `χ_l(1) = 1` and `|χ_l| = 1` on the unit circle.
`kFiniteFunctions`, `principalSeries`, `principalSeriesCharacter`, `Iwasawa.diagonalUnits` and
`upperUnipotent` are the Library's. Unprefixed names below are in the namespace
`Langlands.Archimedean.ComplexBlockJacquet`.

## Definitions

* `blockShiftChar k χ l z = χ_l(z) (|z|²)^{-(k+1)/2}`: the characters of `GL_a(ℂ)` attached to the
  first `a` positions.
* `IsBlockDominant e a k`: `Re e_a = Re e_{a+j}` for `j ≤ k` (`tie`), `Re e_{l+1} ≤ Re e_l` for
  `l < a` (`ord`) and `Re e_{l+1} < Re e_l` for `l + 1 = a` (`gap`).
* `blockStep h g = ∫_{M_{(k+1)×a}(ℂ)} h(n̄(X) g) dX` (the partial Jacquet integral `T_P h`;
  Lebesgue measure on `Fin (k+1) → Fin a → ℂ`, `X` read as a matrix by `Matrix.of`).
* `blockPair φ h g₁ = ∫_{U(k+1)} φ(κ₂) · blockStep h (diag(g₁, κ₂)) dκ₂` for
  `φ : GL_{k+1}(ℂ) → ℂ` and `g₁ ∈ GL_a(ℂ)`.

## The statement

`ComplexBlockJacquetStatement` assumes `ComplexBlockChartIntegrableStatement`, which is only
stated, not yet proved, in the Library. Under that assumption it says the following.

Let `χ` be phase-power characters with exponents `e` satisfying the three conditions of
`IsBlockDominant e a k`, given as separate hypotheses. For every `U(a+k+1)`-finite function `h` of
`principalSeries ℂ (a+k+1) χ`:

1. `X ↦ h(n̄(X) κ)` is integrable for every `κ ∈ U(a+k+1)`;
2. for every continuous `φ` on `GL_{k+1}(ℂ)`, `blockPair φ h` is a `U(a)`-finite function of
   `principalSeries ℂ a (blockShiftChar k χ)`.

It is proved as `Langlands.Archimedean.complexBlockJacquet`, from `integrable_block` and
`blockPair_mem`.

Provenance. Derived, internal infrastructure: the standard partial Jacquet (intertwining) integral
along a maximal parabolic subgroup, here with a tied last block. It mirrors the published
`ComplexPartialJacquet` and makes no claim beyond the Lean statement.

## Proof

### Change of variables (section `RowMul`)

* `rowMulLinearEquiv`: `X ↦ X B`, row by row (`LinearEquiv.piCongrRight` of
  `ComplexPartialJacquet.vecMulLinearEquiv`). `det_rowMulLinearEquiv`: its complex determinant is
  `(det B)^{k+1}`, by `LinearMap.det_pi`.
* `isAddHaarMeasure_volume_rows` (instance): Lebesgue measure on `Fin (k+1) → Fin a → ℂ` is an
  additive Haar measure.
* `rowMulEquiv`, `map_rowMulEquiv`: Lebesgue measure is mapped to `|det B|^{-2(k+1)}` times
  itself. The real determinant is `normSq(det B)^{k+1}` (`LinearMap.det_restrictScalars`); then
  apply `Measure.map_linearMap_addHaar_eq_smul_addHaar`.
* `integral_rowMul_eq`: `∫ f(X B) dX = |det B|^{-2(k+1)} ∫ f`.

### Block matrices (section `Group`)

* `blockDiagGL_mul`: `diag(g₁, g₂) diag(g₁', g₂') = diag(g₁g₁', g₂g₂')`.
* `blockDiagGL_diagonalUnits`: `diag(diag(z), 1) = diag(z, 1, …, 1)` (`Fin.addCases`).
* `blockDiagGL_mem_upperUnipotent`: `diag(u, 1)` is upper unipotent for upper unipotent `u`.
* `blockLower_mul_blockDiag_one`, `blockLowerGL_mul_blockDiagGL`:
  `n̄(X) diag(g, 1) = diag(g, 1) n̄(X g)`.

### Characters (section `Shift`)

* `isPhasePower_blockShift`: `blockShiftChar k χ` is phase-power with exponents
  `e_l − (k+1)/2`.
* `principalSeriesCharacter_addCases`: if `χ_j(1) = 1` for `j ≥ a`, then
  `principalSeriesCharacter (a+k+1) χ (z, 1, …, 1) · (∏_i |z_i|²)^{-(k+1)} =
  principalSeriesCharacter a (blockShiftChar k χ) z`. Factor by factor, the exponents
  `(a+k)/2 − i − (k+1)` and `−(k+1)/2 + (a−1)/2 − i` agree (`cpow_combine`).

### Equivariance (section `Step`)

`blockStep_mul`: for `b = diag(z) u` in the Borel subgroup of `GL_a(ℂ)`,
`T_P h(diag(b g₁, g₂)) = principalSeriesCharacter a (blockShiftChar k χ) z · T_P h(diag(g₁, g₂))`.
Proof:

1. Write `diag(b g₁, g₂) = diag(b, 1) diag(g₁, g₂)` and `n̄(X) diag(b, 1) = diag(b, 1) n̄(X b)`
   (`of_mul_eq_of_vecMul`). Here `diag(b, 1) = diag(z, 1, …, 1) · diag(u, 1)` with an upper
   unipotent second factor.
2. The principal-series property of `h` gives the factor
   `principalSeriesCharacter (a+k+1) χ (z, 1, …, 1)`.
3. The substitution `X ↦ X b` (`integral_rowMul_eq`, `det b = ∏ z_i`) gives
   `(∏ |z_i|²)^{-(k+1)}`.
4. These two factors combine by `principalSeriesCharacter_addCases`.

### Integrability, continuity and finiteness (section `Pair`)

* `tail_h`: `IsBlockDominant` implies the tail condition of `ComplexBlockChartIntegrableStatement`
  for the exponents `Re e_{l+1} − Re e_l − 1`. These are `≤ −1` and `< −1` at `l = a − 1`, so
  `ComplexPartialSqIntegral.tailCondition_of_le` applies.
* `integrable_block`: dominated by `C · blockChartBound` (`ComplexBlockLimit.norm_le_block`),
  which is integrable by the assumed statement.
* `continuous_blockStep`: `t ↦ T_P h(diag(f₁ t, f₂ t))` is continuous for continuous maps `f₁, f₂`
  into the unitary groups on a first-countable space (`continuous_of_dominated`).
  `norm_blockStep_le` bounds `T_P h` on `U(a+k+1)` by `∫ C · blockChartBound`.
* `integrable_of_continuous_unitary`: continuous functions on `U(n)` are `unitaryHaar`-integrable.
* `blockPair_mul`: `blockPair φ h (diag(z) u g₁) = principalSeriesCharacter a (blockShiftChar k χ) z ·
  blockPair φ h g₁`, from `blockStep_mul`.
* `continuous_blockPair`: `κ ↦ blockPair φ h κ` is continuous on the matrix unitary group, by
  dominated convergence with a constant bound.
* `blockPairOn`: `f ↦ (κ ↦ blockPair φ f κ)` is linear on any submodule of the principal series.
  The `X`- and `κ₂`-integrals are additive by `integrable_block` and
  `integrable_of_continuous_unitary`.
* `blockPair_rightTranslation`: right translation of `f` by `diag(κ, 1)` becomes right translation
  of `blockPair φ f` by `κ`.
* `finiteDimensional_blockPair`: the right `U(a)`-translates of `κ ↦ blockPair φ h κ` lie in the
  image under `blockPairOn` of the finite-dimensional span of the `U(a+k+1)`-translates of `h`.
* `blockPair_mem`: the function `κ ↦ blockPair φ h κ` on `U(a)` satisfies the hypotheses of
  `ComplexPrincipalSeriesExtension.extension_mem_kFiniteFunctions`: continuity, finiteness, and
  equivariance under `phaseMatrix` (via `ComplexPartialJacquet.phaseMatrix_toUnits` and
  `blockPair_mul`). The resulting extension agrees with `blockPair φ h` on `diag(z) u κ`
  (Iwasawa decomposition, `exists_diagonalUnits_mul_upperUnipotent_mul_unitary`), because both
  sides satisfy the same equivariance.

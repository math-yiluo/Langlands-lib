# The partial Jacquet integral along `P_{m,1}`

Lean module: `Langlands.Representation.Archimedean.PartialJacquetIntegral`.

For a function `h` of the principal series of `GL_{m+1}(ℝ)` this module defines the partial
Jacquet integral

`T h(g) = ∫_{ℝ^m} h(J(x,1) ι(g)) dx`,  `g ∈ GL_m(ℝ)`  (`jacquetStep`),

where `J(x,1)` is the identity matrix with last row `(x, 1)` (`chartGL`) and `ι(g) = diag(g, 1)`
(`iotaGL`). The main result `jacquetStep_mem` says the following. Suppose the characters are
strictly dominant signed powers and `h` is `O(m+1)`-finite. Then the integral converges and
`T h` is an `O(m)`-finite function of the principal series of `GL_m(ℝ)` for the shifted
characters `χ_l |·|^{-1/2}`. This is the integral over `N̄_P` in "induction in stages" through
the maximal parabolic subgroup `P_{m,1}`. It is used for the Langlands quotient.

Declarations without a prefix are in the namespace `Langlands.Archimedean.PartialJacquet`.
`MaximalParabolicIntegration`, `ParabolicChartBound` and `PrincipalSeriesExtension` are the
modules of the same name.

## Characters

* `IsSignedPower χ e` (structure) collects three conditions on every position `l`:
  `χ_l(x) = χ_l(sgn x) |x|^{e_l}` (the hypothesis of the Library's extension lemma),
  `χ_l(1) = 1`, and `‖χ_l(−1)‖ = 1`. Consequences: `‖χ_l(x)‖ = |x|^{Re e_l}`
  (`IsSignedPower.norm`) and `χ_l(x) ≠ 0`.
* `dualChar χ = χ⁻¹`, a signed power with exponents `−e` (`IsSignedPower.dual`).
  `shiftChar χ = χ |·|^{−1/2}`, a signed power with exponents `e − 1/2`
  (`IsSignedPower.shift`).
* `IsStrictlyDominant e m`: `Re e_{l+1} < Re e_l` for every `l < m`, so for the positions
  `0, …, m` of `GL_{m+1}`. It passes to the shifted exponents on `GL_m`
  (`IsStrictlyDominant.shift`).
* `normExponent e N l = Re e_l + (N−1)/2 − l` is the exponent of `‖χ δ^{1/2}‖`
  (`norm_principalSeriesCharacter`). `chartExponent e l = (Re e_{l+1} − Re e_l − 1)/2` is the
  exponent of the chart bound. It is `< −1/2` under strict dominance (`chartExponent_lt`).

## Chart identities and changes of variables

* `chartGL_mul_iotaGL`: `J(x,1) ι(g) = ι(g) J(x g, 1)`.
* `chartGL_mul_dlastGL`: `J(x,1) d(s) = d(s) J(s⁻¹x, 1)` for `d(s) = diag(1, …, 1, s)`.
* `chartGL_mul_chartGL_neg`: `J(x,1) J(−x,1) = 1`.
* `chartGL` and `iotaGL` are continuous (`continuous_chartGL`, `continuous_iotaGL`).
* For an invertible matrix `B`, `x ↦ x B` is a measurable equivalence (`vecMulEquiv`).
  Lebesgue measure transforms by `|det B|⁻¹` (`map_vecMulEquiv`, from
  `Measure.map_linearMap_addHaar_eq_smul_addHaar`). This gives `integral_vecMul_smul`,
  `integral_vecMul_eq` and `integrable_comp_vecMul`.

## Bounds and convergence

* `norm_le_partialSq`: for `h` in the principal series of a signed power `χ` with `‖h‖ ≤ C` on
  `O(m+1)`, `‖h(J(x,1)κ)‖ ≤ C ∏_{l<m} r_{l+1}(x)^{chartExponent e l}` for `κ ∈ O(m+1)`. This is
  `ParabolicChartBound.norm_le_chart` with `σ = normExponent e (m+1)`.
* `norm_le_of_mem_principalSeries`: under strict dominance, the bound
  `C ∏ (1 + x_l²)^{chartExponent e l}` holds. It is integrable, so `x ↦ h(J(x,1)κ)` is
  integrable (`integrable_chart`).
* `continuous_jacquetStep_unitary`: `κ ↦ T h(κ)` is continuous on `O(m)`. This follows from
  `continuous_of_dominated`, because the bound above does not depend on `κ`.

## Equivariance and finiteness

* `principalSeriesCharacter_lastCases`: if `χ_m(1) = 1`, then
  `χδ^{1/2}_{m+1}(a, 1) · (∏ |a_i|)⁻¹ = (χ|·|^{−1/2}) δ^{1/2}_m(a)`.
* `jacquetStep_mul`: `T h(diag(a) u g) = (χ|·|^{−1/2})δ^{1/2}_m(a) · T h(g)`. Write
  `b = diag(a) u`. Then `J(x,1) ι(b g) = ι(b) J(x b, 1) ι(g)`, and `ι(b) = diag(a, 1) ι(u)` with
  `ι(u)` upper unipotent. The substitution `x ↦ x b` contributes `|det b|⁻¹ = ∏ |a_i|⁻¹`.
* `jacquetStep_rightTranslation`: `T(R(ι(k)) f)(g) = T f(g k)`.
* `jacquetStepOn` is `T` restricted to `O(m)`, as a linear map on a subspace of the principal
  series (additivity uses `integrable_chart`). `finiteDimensional_jacquetStep`: the right
  translates of `T h` by `O(m)` lie in the image under `jacquetStepOn` of the span of the right
  translates of `h` by `O(m+1)`. That span is finite-dimensional because `h` is `O(m+1)`-finite.

## The main result

`jacquetStep_mem`: let `χ` be a signed power with `IsStrictlyDominant e m`, and let `h` be an
`O(m+1)`-finite function of the principal series of `χ`. Then `T h` is an `O(m)`-finite function
of the principal series of `shiftChar χ`. Proof:

* `φ(κ) = T h(κ)` on `O(m)` is continuous and `O(m)`-finite (see above).
* `φ` transforms under the diagonal sign matrices by the character of `shiftChar χ`
  (`signDiagonal_toUnits` and `jacquetStep_mul`).
* The accepted extension lemma `PrincipalSeriesExtension.extension_mem_kFiniteFunctions` gives an
  element `E` of the `O(m)`-finite principal series of `shiftChar χ` with `E = φ` on `O(m)`.
* `T h = E` on all of `GL_m(ℝ)`. Write `g = diag(a) u k` with
  `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`. Both functions transform by the
  same character (`jacquetStep_mul`, and principal-series membership of `E`), and they agree at
  `k`.

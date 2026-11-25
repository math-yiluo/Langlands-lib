# The limit along `P_{a,k+1}` of `GL_{a+k+1}(ℝ)` in value form

Lean module: `Langlands.Representation.Archimedean.RealBlockLimitValue`.

This module was written for the proof of
`RealStandardIrreducibleCriterionStatement`; the Library's proof of that statement (in
`RealLargeLanglandsQuotientInjectiveProof`) does not import this module. It is a helper for the
reversal statement for character lists with ties (`RealCharacterReverseKernel`). The module
`RealBlockLimit` proves the limit argument along the maximal parabolic subgroup `P_{a,k+1}` in
*vanishing* form: if every matrix coefficient `g ↦ ∫ u(κ g) h(κ) dκ` vanishes, then so does the
limit value `∫∫ u(m) T_P h(m)`. The reversal argument needs the *value* form: the normalized
matrix coefficients along `d(s)` converge to that limit value, whether or not they vanish. This
module proves it by the same three dominated-convergence steps as
`RealBlockLimit.integral_mul_blockStep_eq_zero`.

Notation (all from the modules `RealBlockLimit`, `RealBlockJacquet` and the statement
`RealBlockParabolicIntegrationStatement`): `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`, `O(N)` is
`unitaryCompact ℝ N` with the Haar probability measure `RealPrincipalSeriesDuality.haarK N`.
`n̄(X)` (`blockLowerGL`) is the lower unipotent block matrix `[[1, 0], [X, 1]]` for
`X ∈ M_{(k+1)×a}(ℝ) = Fin (k+1) → Fin a → ℝ` (Lebesgue measure), and `diag(g₁, g₂)` is
`blockDiagGL g₁ g₂`. `tailEntries s` is the vector with entries `1` before position `a` and `s`
from position `a` on, and `d(s) = dTail s = diag(1_a, s·1_{k+1})` is the corresponding diagonal
matrix. `Φ u h s κ₁ κ₂ X = u(n̄(s⁻¹X) diag(κ₁, κ₂)) · h(n̄(X) diag(κ₁, κ₂))`.
`blockStep h g = T_P h(g) = ∫ h(n̄(X) g) dX`. `IsSignedPower χ e` (module
`PartialJacquetIntegral`) means `χ_l(x) = χ_l(sgn x) |x|^{e_l}`, `χ_l(1) = 1` and
`‖χ_l(−1)‖ = 1`; `dualChar χ` is `l, x ↦ (χ_l x)⁻¹`. `IsBlockDominant e a k` (module
`RealBlockJacquet`) says `Re e_{a+j} = Re e_a` for `j ≤ k`, `Re e_{l+1} ≤ Re e_l` for `l < a` and
`Re e_a < Re e_{a−1}` when `a ≥ 1`.

Declarations without a prefix are in the namespace `Langlands.Archimedean.RealBlockLimitValue`.
There is no statement (`def … : Prop`) in this module; it contains definitions and theorems only.

## Definitions

* `seqUnit m : ℝˣ` is the unit `m + 1` (`seqUnit_val`).
* `tailFactor a k χ s` is the value at `d(s)` of the character of the principal series of
  `χ⁻¹`: `principalSeriesCharacter ℝ (a+(k+1)) (dualChar χ) (tailEntries s)`.
* `limitValue u h = ∫_{O(a)} ∫_{O(k+1)} u(diag(κ₁, κ₂)) · T_P h(diag(κ₁, κ₂)) dκ₂ dκ₁`.

## Results

* `tailFactor_ne_zero`: for `IsSignedPower χ e`, `tailFactor a k χ s ≠ 0`. Its norm is a product
  of positive powers `|s_l|^{…}` (`norm_principalSeriesCharacter` for the dual characters).
* `exists_integral_dTail_eq` (assumes `RealBlockParabolicIntegrationStatement`): there is a real
  `c > 0`, depending only on `a, k`, such that for all `χ, e` with `IsSignedPower χ e`, all `u` in
  `principalSeries ℝ (a+(k+1)) (dualChar χ)`, all `h` in `principalSeries ℝ (a+(k+1)) χ` and all
  real `s > 0`,

  `∫_{O(a+k+1)} u(κ d(s)) h(κ) dκ = c · tailFactor a k χ s · ∫_{O(a)} ∫_{O(k+1)} ∫_X Φ u h s κ₁ κ₂ X`.

* `tendsto_Φ` (assumes `RealBlockChartIntegrableStatement`): for `IsSignedPower χ e`,
  `IsBlockDominant e a k`, `u` and `h` as above, along `s = m + 1` the triple integral
  `∫_{O(a)} ∫_{O(k+1)} ∫_X Φ u h (m+1) κ₁ κ₂ X` tends to `limitValue u h`.
* `exists_tendsto` (assumes both statements): there is a complex `c ≠ 0`, depending only on
  `a, k`, such that for all `χ, e, u, h` as in `tendsto_Φ`,

  `(c · tailFactor a k χ (m+1))⁻¹ · ∫_{O(a+k+1)} u(κ d(m+1)) h(κ) dκ → limitValue u h`

  as `m → ∞`.

Provenance. Derived. This is the standard leading-term (Langlands lemma) argument along a maximal
parabolic subgroup, internal infrastructure. It restates the content of the proof of
`RealBlockLimit.integral_mul_blockStep_eq_zero` with the limit value kept. It makes no claim beyond
the Lean statements. The two assumed statements `RealBlockChartIntegrableStatement` and
`RealBlockParabolicIntegrationStatement` are proved in the Library as `realBlockChartIntegrable`
(`RealBlockChartIntegralProof`) and `realBlockParabolicIntegration`
(`RealBlockParabolicIntegrationProof`); every theorem of this module that uses them takes them as
explicit hypotheses.

## Proof

The local instances `measurableSpaceK`, `secondCountableTopology_unitaryCompact` (from
`RealBlockLimit`) and `borelSpaceK_lv` (the measurable structure on `O(n)` is the Borel one) supply
the measurability needed for integrals over products of orthogonal groups.

`exists_integral_dTail_eq`. Take the constant `c > 0` of `RealBlockParabolicIntegrationStatement`
for the parabolic `P_{a,k+1}`. Apply it to `F(y) = u(y d(s)) h(y)`. `F` is smooth (product of the
smooth functions `u ∘ R_{d(s)}` and `h`) and modulus-covariant, because the characters of `u` and
`h` multiply to the modulus character (`principalSeriesCharacter_dual_mul`). The statement then
writes `∫_{O(a+k+1)} F` as `c` times the triple integral of `F(n̄(X) diag(κ₁, κ₂))`. Pointwise,
`n̄(X) diag(κ₁, κ₂) d(s) = d(s) n̄(s⁻¹X) diag(κ₁, κ₂)` (`blockDiagGL_mul_dTail`,
`blockLowerGL_mul_dTail`), and `u(d(s) y) = tailFactor · u(y)` by the equivariance of `u`. So
`F(n̄(X) diag(κ₁, κ₂)) = tailFactor · Φ u h s κ₁ κ₂ X`, and the constant comes out of the
integrals.

`tendsto_Φ`. Bound `u` and `h` on `O(a+k+1)` by constants `C_u`, `C_h`
(`exists_bound_unitaryCompact`). Let `γ_l = max((Re e_{l+1} − Re e_l − 1)/2, −1)` and
`D(X) = C_u C_h blockChartBound γ X`. `D` is integrable by `RealBlockChartIntegrableStatement` and
`tail_max`. By `norm_Φ_le` (from `RealBlockLimit`), `‖Φ u h (m+1) κ₁ κ₂ X‖ ≤ D(X)` for all `m`.
Dominated convergence is applied three times:

1. the `X`-integral, pointwise in `(κ₁, κ₂)`, with dominating function `D`: as `m → ∞`,
   `(m+1)⁻¹ X → 0`, so `n̄((m+1)⁻¹X) → n̄(0) = 1` (`blockLowerGL_zero`), and by continuity of `u`
   the integrand tends to `u(diag(κ₁, κ₂)) · h(n̄(X) diag(κ₁, κ₂))`;
2. the `κ₂`-integral, with the constant bound `∫ D`;
3. the `κ₁`-integral, with the same constant bound.

Measurability comes from `AEStronglyMeasurable.integral_prod_right'` and `continuous_Φ`. The limit
is `limitValue u h`.

`exists_tendsto`. Take `c` from `exists_integral_dTail_eq` (as a complex number, nonzero). By that
identity, at `s = m + 1` the normalized coefficient equals the triple integral, because
`c · tailFactor ≠ 0` (`tailFactor_ne_zero`). Conclude by `tendsto_Φ`.

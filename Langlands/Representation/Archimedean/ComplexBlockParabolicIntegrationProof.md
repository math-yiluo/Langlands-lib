# Proof of the integration formula along `P_{a,k}`

Lean module: `Langlands.Representation.Archimedean.ComplexBlockParabolicIntegrationProof`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It proves the induction step of the integration
formula along the maximal parabolic subgroup `P_{a,k}`. As a consequence it proves the Library
statement `ComplexBlockParabolicIntegrationStatement` as the theorem
`Langlands.Archimedean.complexBlockParabolicIntegration`. That statement is also the target of the
proof task Task 7162.

Notation is as in `ComplexBlockModulusBound` and `ComplexBlockParabolicSlices`, the two tools
modules it imports.

* `n̄(X) = [[1, 0], [X, 1]]` and `diag(g₁, g₂)`;
* `ι(g) = diag(g, 1)` and `J(v, 1)`;
* `U(n)` with its Haar probability measure `unitaryHaar n`, and Lebesgue measure on
  `M_{k×a}(ℂ) = (Fin k → Fin a → ℂ)` and on `ℂ^m`;
* `c_m = chartConstant m > 0`, the constant of the published formula for `P_{m,1}`.

Unprefixed names are in the namespace `Langlands.Archimedean.ComplexBlockParabolicProof`.

## The statements

`BlockFormula a k` is the integration formula for fixed `a, k`, without the integrability clause.
There is `c > 0` such that for every `F` in `principalSeries ℂ (a+k) (modulusCharacter (a+k))`,

`∫_{U(a+k)} F(κ) dκ = c ∫_{U(a)} ∫_{U(k)} ∫_{M_{k×a}(ℂ)} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁`.

`ComplexBlockParabolicStepStatement`: for all `a, k ∈ ℕ`, `BlockFormula a k` implies
`BlockFormula a (k + 1)`. It is proved as `Langlands.Archimedean.complexBlockParabolicStep`.

`Langlands.Archimedean.complexBlockParabolicIntegration : ComplexBlockParabolicIntegrationStatement`
combines `BlockFormula a k` for all `k` (`blockFormula`, by induction from `blockFormula_zero` and
`blockFormula_succ`) with the integrability clause `integrable_clause`.

Provenance. Derived, internal. The route is a variant of the one sketched in
`ComplexBlockParabolicIntegrationStatement.md` ("Intended proof"). Instead of a Gaussian model of
the last `k` rows, the formula is obtained by induction on `k` from the published formula for
`P_{m,1}`:

* `ComplexMaximalParabolicIntegration.integral_eq_chart`:
  `∫_{U(m+1)} F = c_m ∫_{ℂ^m} ∫_{U(m)} F(ι(κ) J(v,1)) dκ dv`;
* `ComplexJacquetLimit.integral_eq_chart'`:
  `∫_{U(m+1)} F = c_m ∫_{U(m)} ∫_{ℂ^m} F(J(v,1) ι(κ)) dv dκ`.

These are only ever applied to smooth slices of `F`. No literature statement is claimed. The
resulting constant is `c_{a,k+1} = c_{a+k} c_{a,k} / c_k`.

## Proof

### The integrability clause and the case `k = 0`

* `integrable_clause`: for `F` in the principal series of the modulus character,
  `X ↦ F(n̄(X) diag(κ₁, κ₂))` is integrable for all `κ₁ ∈ U(a)` and `κ₂ ∈ U(k)`. It is dominated by
  `C · blockBound a k` (`norm_le_blockBound`, `integrable_blockBound`).
* `blockDiagGL_zero`: `diag(κ₁, κ₂) = κ₁` when `k = 0`.
* `blockFormula_zero`: `BlockFormula a 0` with `c = 1`. Here `M_{0×a}(ℂ)` is a point of measure `1`
  (`integral_unique`) and `n̄(X) = 1`.

### Auxiliary facts (sections `Points`, `ChartIota`)

* `det_blockLowerGL`, `norm_det_point`: `|det(n̄(X') diag(κ₁, τ))| = 1` for unitary `κ₁, τ`.
* `normSqC_of_norm_one`, `norm_det_inv_of_norm_one`.
* `continuous_point`: continuity of `(κ₁, τ, X') ↦ n̄(X') diag(κ₁, τ)`.
* `integrable_iota_chart`: `v ↦ F(ι(g) J(v,1))` is integrable for every `g`. Proof: since
  `ι(g) J(v,1) = J(v g⁻¹, 1) ι(g)` (`ComplexJacquetLimit.iotaGL_mul_chartGL`), this is
  `integrable_chart_iota` after the substitution `v ↦ v g⁻¹`.
* `integral_norm_iota_chart`: if `|det g| = 1`, then `∫ ‖F(ι(g) J(v,1))‖ dv = chartNorm F g`.

### Step 1 (section `StepOne`)

Let `F` lie in the principal series of the modulus character of `GL_{a+k+1}(ℂ)`. Set

`Z(F) = ∫_{U(a)} ∫_{U(k)} ∫_{M_{k×a}} ∫_{ℂ^{a+k}} F(ι(n̄(X')) J(v,1) ι(diag(κ₁, τ))) dv dX' dτ dκ₁`

(`chartIntegral`). `step_one`: if `BlockFormula a k` holds with constant `c₀`, then
`∫_{U(a+k+1)} F = c_{a+k} c₀ Z(F)`.

1. `integral_eq_chart` for `m = a + k` writes `∫_{U(a+k+1)} F` as `c_{a+k} ∫_v ∫_{U(a+k)} F(ι(κ) J(v,1))`.
2. For fixed `v`, the Levi slice `g ↦ F(ι(g) J(v,1)) |det g|^{−2}`
   (`ComplexMaximalParabolicIntegration.leviSlice`) lies in the principal series of the modulus
   character of `GL_{a+k}(ℂ)` (`leviSlice_mem`). The hypothesis `BlockFormula a k` therefore
   applies to it. At `κ ∈ U(a+k)` and at `n̄(X') diag(κ₁, τ)` the factor `|det g|^{−2}` is `1`.
3. `step_one_fubini` moves the `v`-integral inside. Let `Ω = U(a) × (U(k) × M_{k×a})`.
   * For fixed `v`, the integrand is dominated by `C_v · blockBound a k (X')` on `Ω`. This is
     `norm_le_blockBound` for the Levi slice, and gives `integral_prod_prod`.
   * The joint integrand on `Ω × ℂ^{a+k}` is integrable by `integrable_prod_iff`. Its
     `v`-sections are integrable by `integrable_iota_chart`. Its `v`-norm integral is
     `chartNorm F (n̄(X') diag(κ₁, τ))`, which is dominated by a constant times
     `blockBound a k (X')`. This last bound is `norm_le_blockBound` applied to the norm-covariant
     function `chartNorm F` (`normCov_chartNorm`, `chartNorm_le`).
   * `integral_integral_swap` exchanges the integrals.
   * For each point of `Ω`, the substitution `v ↦ v diag(κ₁, τ)⁻¹` (`integral_vecMul_eq`, Jacobian
     `1`) together with `ι(D) J(v,1) = J(v D⁻¹, 1) ι(D)` turns the integrand into that of `Z(F)`.

### Step 2 (section `StepTwo`)

`step_two`: `∫_{U(a)} ∫_{U(k+1)} ∫_{M_{(k+1)×a}} F(n̄(X) diag(κ₁, κ₂)) dX dκ₂ dκ₁ = c_k Z(F)`.

For fixed `κ₁ ∈ U(a)` (`step_two_inner`) the argument has the following steps.

a. For `κ₂ ∈ U(k+1)`, the substitution `X ↦ κ₂ X` (`integral_leftMul_eq`, Jacobian `1`) and
   `diag(1, h) n̄(X) diag(κ₁, 1) = n̄(h X) diag(κ₁, h)` (`blockDiagGL_mul_blockLowerGL`) show the
   following. The inner integral is `∫_X T_X(κ₂) dX`, where
   `T_X = sliceT F (slicePoint κ₁ X)` is the slice `h ↦ F(diag(1, h) n̄(X) diag(κ₁, 1)) |det h|^{2a}`
   (`sliceT_point`, `integral_sliceT_point`).
b. `integral_integral_swap` exchanges `κ₂` and `X`. The joint integrability comes from
   `integrable_prod_of_bounded`: the sections are integrable by `integrable_sliceT_point`, and
   their norm integrals equal `blockNorm F κ₁ κ₂ ≤ C ∫ blockBound`
   (`integral_norm_sliceT_point`, `blockNorm_le`).
c. `T_X` lies in the principal series of the modulus character of `GL_{k+1}(ℂ)` (`sliceT_mem`).
   So `integral_eq_chart'` for `m = k` gives
   `∫_{U(k+1)} T_X = c_k ∫_{U(k)} ∫_{ℂ^k} T_X(J(w,1) ι(τ))`.
d. The last double integral is a single integral over `U(k) × ℂ^k`. The integrand is dominated
   by `C_X ∏_l (1 + |w_l|²)^{−2}` (`norm_le_chartBound`).
e. `integral_integral_swap` exchanges `X` and `(τ, w)`. The joint integrability uses
   `integrable_prod_iff`:
   * the `X`-sections are integrable by `integrable_sliceT_point`;
   * the norm integral over `X` equals `blockNorm F κ₁ (J(w,1) ι(τ))`. This is dominated by a
     constant times `∏_l (1 + |w_l|²)^{−2}`, which is `norm_le_chartBound` for the norm-covariant
     function `blockNorm F κ₁` (`normCov_blockNorm`).
f. For `h = J(w,1) ι(τ)` one has `|det h| = 1` (`norm_det_chart_iota`). So
   `∫_X T_X(h) = ∫_X F(n̄(X) diag(κ₁, h))` (`integral_sliceT_point`).
g. The integral over `U(k) × ℂ^k` is split back into iterated integrals.
h. For fixed `τ`, take the integral over `(w, X) ∈ ℂ^k × M_{(k+1)×a}` and change coordinates
   with `rowsChart`: `X = [X'; x]` and `v = (x, w) ∈ ℂ^{a+k}` (`integral_rowsChart`,
   `integrable_rowsChart`). The chart identity `blockLowerGL_mul_blockDiagGL_chart` and
   `Fin.append_castAdd_natAdd` turn the integrand into that of `Z(F)`. The integrability on
   `ℂ^k × M_{(k+1)×a}` again comes from `integrable_block_diag` and `blockNorm`.

`continuous_sliceT_point` provides the measurability of the integrands. It is stated for general
continuous maps into `GL_{k+1}(ℂ)` and `M_{(k+1)×a}(ℂ)`.

### The induction

`blockFormula_succ`: by `step_one` and `step_two`,

`∫_{U(a+k+1)} F = c_{a+k} c₀ Z(F) = (c_{a+k} c₀ / c_k) · (c_k Z(F))`,

and `c_k Z(F)` is the right side of the formula for `P_{a,k+1}`. Since `c_m > 0`
(`chartConstant_pos`), the constant `c_{a+k} c₀ / c_k` is positive. `blockFormula` is the induction
on `k`.

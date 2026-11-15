# Infinitesimal invariance of the integral over `U(n)` of products of principal-series functions

Module: `Langlands.Representation.Archimedean.ComplexDuality.LieInvariance`.

## Purpose and provenance

This module is internal infrastructure for proving
`Langlands.Archimedean.ComplexStandardDualityStatement` (module
`Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction`). That statement asks
for a pairing between the complex principal series with pointwise inverse characters that is
invariant under `𝔤 = 𝔤𝔩_n(ℂ)` and `K = U(n)`. The intended pairing is
`Q(f, h) = ∫_{U(n)} f(k) h(k) dk`. This module proves its `𝔤`-invariance:
`Q(R(X) f, h) + Q(f, R(X) h) = 0` for every complex matrix `X`.

The mathematics is standard: the product `f h` transforms on the left under the upper
triangular Borel subgroup `B` by its modulus character `δ_B`, and the integral over `K` of such
functions is a `G`-invariant functional on these functions (for example Knapp, *Representation
Theory of Semisimple Groups: An Overview Based on Examples*, Chapter VII, the compact picture of
induced representations). The module does not use that group-level statement or any integration
formula. It proves only the infinitesimal statement directly, by integration by parts on `U(n)`
along the left-invariant vector fields. This route and all auxiliary declarations belong to
this formalization; the module cites no other literature.

Library definitions used: `principalSeries`, `principalSeriesCharacter`, `rightDerivative`,
`matrixModel`, `unitaryCompact`, `upperUnipotent`, `Iwasawa.diagonalUnits`, and from
`PrincipalSeriesStability`, `unitsExtension` (the extension of a function on `GL_n(ℂ)` to all
matrices by `0` off the invertible ones), `contDiffOn_unitsExtension`, `unitsExtension_val`,
`differentiableAt_unitsExtension`, `rightDerivative_eq_fderiv` and `contMDiff_rightDerivative`.

Throughout, `n` is a natural number, `Langlands.GeneralLinear n ℂ` is `GL_n(ℂ)`, matrices are
`Matrix (Fin n) (Fin n) ℂ` viewed as a real normed space with the operator norm, and `fderiv ℝ`
is the real Fréchet derivative. `E_ab` is the matrix unit `Matrix.single a b 1`.

## Main theorem

`Langlands.Archimedean.ComplexDuality.integral_rightDerivative_mul_add_eq_zero`. Assume
`MeasurableSpace` and `BorelSpace` structures on `unitaryCompact ℂ n` and a measure `μ` on it
that is left invariant (`μ.IsMulLeftInvariant`) and finite (`IsFiniteMeasure μ`). Let
`χ χ' : ℕ → ℂˣ → ℂ` with `χ i z * χ' i z = 1` for all `i, z`. Let `f ∈ principalSeries ℂ n χ`
and `h ∈ principalSeries ℂ n χ'`, and let `X` be a complex `n × n` matrix. Then

`(∫ k, R(X) f (k) · h(k) ∂μ) + ∫ k, f(k) · R(X) h (k) ∂μ = 0`,

where `R(X) = rightDerivative (matrixModel ℂ n) X` and `k` runs over `unitaryCompact ℂ n`
(coerced to `GL_n(ℂ)`). Both integrals are Bochner integrals. The proof shows that both
integrands are continuous, hence integrable, so the statement is not vacuous.

## Proof route

Write `Φ = f̃ h̃` (`productExtension f h`) for the product of the extensions of `f` and `h`.
`Φ` is `C^∞` on the invertible matrices, and by the product rule and `rightDerivative_eq_fderiv`,
`R(X) f (k) h(k) + f(k) R(X) h (k) = DΦ(k)(k X)`.

*Transformation of `Φ`.* `Φ(u y) = Φ(y)` for `u` upper unipotent, because the two characters at
`a = 1` multiply to `1`. `Φ(diag(a) y) = ∏ᵢ |aᵢ|^{2((n-1)/2 - i)} · |aᵢ|^{2((n-1)/2 - i)} · Φ(y)`,
because `χ i (aᵢ) χ' i (aᵢ) = 1` (`principalSeriesCharacter_mul_eq`).

*Pointwise identity at a unitary `k`.* Put `Z = k X kᴴ`. Since `kᴴ k = 1`, `k X = Z k`, and
`Z = Σ_{a,b} Z_ab E_ab`, so `DΦ(k)(k X) = Σ_{a,b} DΦ(k)(Z_ab E_ab k)`.

- `a < b`: `DΦ(k)(N k) = 0` for strictly upper triangular `N`. Differentiate
  `t ↦ Φ((1 + t N) k) = Φ(k)` at `t = 0` (`fderiv_strictUpper_mul_eq_zero`).
- `a = b`: differentiate `t ↦ Φ(exp(t diag(d)) k)`, where `exp(t diag(d)) = diag(e^{t dᵢ})`.
  The torus transformation makes this `exp(t Λ) Φ(k)` with
  `Λ = Σᵢ 2 Re dᵢ (n - 1 - 2i)`. So `DΦ(k)(diag(d) k) = Λ Φ(k)` (`fderiv_diagonal_mul_eq`).
  The weight `n - 1 - 2i` is `positionWeight n i`.
- `b < a`: `Z_ab E_ab = Re Z_ab (E_ab - E_ba) + Im Z_ab · i(E_ab + E_ba) + conj(Z_ab) E_ba`
  (`single_eq_skew`). The last term is strictly upper triangular and contributes `0`. For the
  first two, the product rule gives
  `D(c Φ)(k)(V k) = Dc(k)(V k) Φ(k) + c(k) DΦ(k)(V k)` with `c = Re (y X yᴴ)_ab` or
  `Im (y X yᴴ)_ab` (`coeffRe`, `coeffIm`). A direct computation gives `Dc(k)(V k) =
  Re Z_bb - Re Z_aa` in both cases (`fderiv_coeffRe_skewRe`, `fderiv_coeffIm_skewIm`). Since
  `coeffRe X a b k = Re Z_ab` and `coeffIm X a b k = Im Z_ab`, this gives
  `DΦ(k)(Z_ab E_ab k) = pairTerm Φ X k a b - 2 (Re Z_bb - Re Z_aa) Φ(k)`.

`fderiv_single_mul_eq` records the three cases in one formula.

The multiples of `Φ(k)` cancel: `Σ_{b<a} (x_b - x_a) = Σᵢ xᵢ (n - 1 - 2i)`
(`sum_sum_ite_lt_sub`), applied to `xᵢ = 2 Re Z_ii`. Hence
`DΦ(k)(k X) = Σ_{b<a} pairTerm Φ X k a b` (`fderiv_mul_eq_sum_pairTerm`).

*Integration.* Each pair term is a sum of two terms `DΨ(k)(Y k)` with `Ψ` of class `C¹` on the
invertible matrices and `Y` skew-Hermitian. For such `Ψ` and `Y`,
`∫ DΨ(k)(Y k) dμ = 0` (`integral_fderiv_mul_eq_zero`): `exp(t Y)` is unitary, so by left
invariance `t ↦ ∫ Ψ(exp(t Y) k) dμ` is constant. Its derivative at `0` is
`∫ DΨ(k)(Y k) dμ`, by differentiation under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). The domination is a uniform bound for the
continuous integrand on the compact set `[-1, 1] × U(n)`. All integrands are continuous on the
compact space `U(n)`, hence integrable for the finite measure `μ`.

## Declarations

The local declarations below except the main theorem are in the namespace
`Langlands.Archimedean.ComplexDuality.LieInvariance`.

### The unitary group as a compact space

- `continuous_unitaryCompact_val`: `k ↦ (k : Matrix)` is continuous on `unitaryCompact ℂ n`.
- The imported `Langlands.Global.isCompact_unitaryMatrix` specializes to the fact that
  `Matrix.unitaryGroup (Fin n) ℂ` is compact (closed, entries bounded
  by `1`).
- `isCompact_unitaryCompact`: `unitaryCompact ℂ n` is compact in `GL_n(ℂ)` (image of the unitary
  group under `Unitary.toUnits`).
- instance `compactSpace_unitaryCompact`: `CompactSpace (unitaryCompact ℂ n)`.
- `exp_smul_mem_unitaryGroup`: for `Yᴴ = -Y` and real `t`, `exp(t • Y)` is unitary.

### Skew-Hermitian directions and coefficient functions

- `skewRe a b = E_ab - E_ba`, `skewIm a b = i E_ab + i E_ba`; `star_skewRe`, `star_skewIm`:
  both are skew-Hermitian (`star Y = -Y`).
- `single_eq_skew`: `Matrix.single a b z = z.re • skewRe a b + z.im • skewIm a b +
  Matrix.single b a (star z)`.
- `reEntryCLM a b`, `imEntryCLM a b`: the real-linear continuous maps `M ↦ (Re M_ab : ℂ)` and
  `M ↦ (Im M_ab : ℂ)`; `reEntryCLM_apply`, `imEntryCLM_apply` evaluate them.
- `coeffRe X a b y = (Re (y X yᴴ)_ab : ℂ)`, `coeffIm X a b y = (Im (y X yᴴ)_ab : ℂ)`;
  `coeffRe_eq`, `coeffIm_eq` write them as entry functionals composed with `y ↦ y X yᴴ`.
- `differentiableAt_sandwich`, `fderiv_sandwich_apply`, `contDiff_sandwich`: `y ↦ y X star y`
  is `C^∞` over `ℝ`, with derivative `V ↦ V X star k + k X star V` at `k`.
- `contDiff_coeffRe`, `contDiff_coeffIm`: the coefficients are `C^∞`.
- `fderiv_coeffRe_apply`, `fderiv_coeffIm_apply`: the derivative at `k` along `V` is the real
  (resp. imaginary) part of the `(a, b)` entry of `V X star k + k X star V`.
- `sandwich_skew_eq`: for `star Y = -Y`,
  `Y k X star k + k X star (Y k) = Y (k X star k) - (k X star k) Y`.
- `fderiv_coeffRe_skewRe`, `fderiv_coeffIm_skewIm`: for `a ≠ b`, the derivative of
  `coeffRe X a b` along `skewRe a b * k`, and of `coeffIm X a b` along `skewIm a b * k`, at `k`
  are both `Re Z_bb - Re Z_aa`, `Z = k X star k` (no unitarity of `k` needed).

### Derivatives of Borel-equivariant functions

- `principalSeriesCharacter_mul_eq`: if `χ i z * χ' i z = 1`, then
  `principalSeriesCharacter ℂ n χ a * principalSeriesCharacter ℂ n χ' a =
  ∏ᵢ (‖aᵢ‖² : ℂ)^((n-1)/2 - i) · (‖aᵢ‖² : ℂ)^((n-1)/2 - i)`.
- `principalSeriesCharacter_mul_one`: the same product at `a = 1` is `1`.
- `ofReal_norm_exp_sq_cpow`: `((‖exp z‖² : ℝ) : ℂ)^s = exp(2 Re z · s)`.
- `fderiv_strictUpper_mul_eq_zero`: if `Φ` is real-differentiable at `y` and
  `Φ(u y) = Φ(y)` for all `u ∈ upperUnipotent n ℂ`, then `DΦ(y)(N y) = 0` for every `N` with
  `N i j = 0` whenever `j ≤ i`.
- `positionWeight n i = n - 1 - 2i` (as a complex number).
- `fderiv_diagonal_mul_eq`: if `Φ` is real-differentiable at `y` and
  `Φ(diag(a) y) = ∏ᵢ (‖aᵢ‖² : ℂ)^((n-1)/2 - i) · (‖aᵢ‖² : ℂ)^((n-1)/2 - i) · Φ(y)` for all
  `a : Fin n → ℂˣ`, then `DΦ(y)(diag(d) y) = (Σᵢ 2 Re dᵢ · positionWeight n i) Φ(y)`.

### Counting identity

- `sum_sum_ite_lt_sub`: for `x : Fin n → ℂ`,
  `Σ_a Σ_b (if b < a then x b - x a else 0) = Σᵢ xᵢ · positionWeight n i`.

### Pointwise identity

- `pairTerm Φ X k a b`: the sum of the derivatives at `k` of `y ↦ coeffRe X a b y * Φ y` along
  `skewRe a b * k` and of `y ↦ coeffIm X a b y * Φ y` along `skewIm a b * k`.
- `single_strictUpper`: for `r < s`, `Matrix.single r s w` vanishes on and below the diagonal.
- `fderiv_single_mul_eq`: under the unipotent invariance and torus transformation hypotheses of
  the two lemmas above at `k`, with `Z = k X star k`,
  `DΦ(k)(Z_ab E_ab k) = (if b < a then pairTerm Φ X k a b else 0) +
  ((if a = b then 2 Re Z_aa · positionWeight n a else 0) -
  (if b < a then 2 Re Z_bb - 2 Re Z_aa else 0)) Φ(k)`.
- `fderiv_mul_eq_sum_pairTerm`: under the same hypotheses and `star k * k = 1`,
  `DΦ(k)(k X) = Σ_a Σ_b (if b < a then pairTerm Φ X k a b else 0)`.

### Products of principal-series functions

- `productExtension f h y = unitsExtension f y * unitsExtension h y`.
- `unitsExtension_unipotent_mul`: for `f ∈ principalSeries ℂ n χ`, `u` upper unipotent and `g`
  invertible, `unitsExtension f (u g) = principalSeriesCharacter ℂ n χ 1 * f g`.
- `unitsExtension_diagonal_mul`: for such `f`,
  `unitsExtension f (diag(a) g) = principalSeriesCharacter ℂ n χ a * f g`.
- `contDiffOn_one_of_infty`: `C^∞` on a set implies `C¹` on it.
- `continuous_fderiv_apply_val`: if `Ψ` is `C¹` on the invertible matrices and `V` is
  continuous, then `k ↦ DΨ(k)(V k)` is continuous on `unitaryCompact ℂ n`.

### Integration

These assume `MeasurableSpace` and `BorelSpace` on `unitaryCompact ℂ n` and a measure `μ`.

- `integrable_of_continuous`: for `μ` finite, continuous functions `unitaryCompact ℂ n → ℂ` are
  `μ`-integrable.
- `integral_fderiv_mul_eq_zero`: for `μ` left invariant and finite, `Ψ` of class `C¹` on the
  invertible matrices and `Yᴴ = -Y`, `∫ k, DΨ(k)(Y k) ∂μ = 0`.
- `Langlands.Archimedean.ComplexDuality.integral_rightDerivative_mul_add_eq_zero`: the main
  theorem above.

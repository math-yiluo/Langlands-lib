# Archimedean Gaussians: Fourier transforms and local zeta integrals

Module `Langlands.Global.Hecke.ArchGaussian`, namespace `Langlands.Global.Hecke`.

This module computes, at the real and complex places, the Fourier transforms and local zeta
integrals of the adapted Gaussian test functions that Tate's thesis (§2.5) uses at the
archimedean places. They are the archimedean inputs of the proof of the global functional
equation of Hecke `L`-functions. The archimedean epsilon factor is the ratio of the
`L`-normalized zeta integrals, `[Z(f̂, χ⁻¹, 1 - s) / L(χ⁻¹, 1 - s)] / [Z(f, χ, s) / L(χ, s)]`
(Tate, *Number theoretic background*, Corvallis Proceedings Part 2 (1979), §3.2, (3.2.1)),
not the ratio of the raw zeta integrals: for the trivial real character and `a = 1` the raw
ratio is `Γ_ℝ(1 - s) / Γ_ℝ(s)`, while the epsilon factor is `1`. This module only computes the
raw integrals; it states nothing about epsilon factors. It is an internal helper.

Notation: `𝐞 x = exp (2π i x)` is Mathlib's `Real.fourierChar` (a `Circle`-valued function,
coerced to `ℂ`); `π` is `Real.pi`; complex powers are Mathlib's `cpow` (principal branch),
which for a positive real base `r` is `r ^ z = exp (z log r)`; `Γ_ℝ(s) = π^{-s/2} Γ(s/2)` and
`Γ_ℂ(s) = 2 (2π)^{-s} Γ(s)` are Mathlib's `Gammaℝ` and `Gammaℂ`. All integrals are for Lebesgue
measure (`volume`) on `ℝ` and on `ℂ`; on `ℂ` this is the area measure `dx dy` for `z = x + i y`.

## Provenance

Internal. The computations are the standard ones of Tate's thesis (Tate, *Fourier analysis in
number fields and Hecke's zeta-functions*, in Cassels–Fröhlich, *Algebraic Number Theory*
(1967), §2.5, the unnumbered computations "k Real" and "k Complex", printed pp. 316–319). Tate
uses twice the area measure at the complex place; here the computations are written for the
plain Lebesgue measure and for characters written as `x ↦ (x/|x|)^p |x|^t` on `ℝ` and
`z ↦ (z/|z|)^N |z|^{2t}` on `ℂ`. The test functions are scaled by the absolute value `b = |a|`
of the element `a` defining the additive character, so that each is (up to a constant) carried
to a function of the same shape by the Fourier transform. The proofs use Mathlib's Gaussian
integrals (`integral_cexp_quadratic`, `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`),
Mathlib's integration of radial functions (`integral_fun_norm_addHaar`), and Mathlib's
integration by parts along a line (`integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`).
The route through the moment recursion for the complex Fourier transform is internal.

## Definitions

- `realGaussian b p x = x ^ p * exp (-(π b x²))`, for `b : ℝ`, `p : ℕ`, `x : ℝ` (complex-valued).
- `realCharFun p t x = (x / |x|) ^ p * |x| ^ t`, for `p : ℕ`, `t : ℂ`, `x : ℝ` (the real
  quotient `x / |x|` is `sgn x` for `x ≠ 0`; the value at `0` is irrelevant for the integrals).
- `cGauss b z = exp (-(2π b) z z̄)`, for `b : ℝ`, `z : ℂ`.
- `cChar u z = exp (2π i (u z + ū z̄))`, for `u, z : ℂ`; this is `𝐞 (2 Re (u z))` (`cChar_eq`).
- `cMoment b u n = ∫ z̄ ^ n * cGauss b z * cChar u z dz`, for `n : ℕ`.
- `complexGaussian b N z = z̄ ^ (N.toNat) * z ^ ((-N).toNat) * exp (-(2π b |z|²))`, for `N : ℤ`:
  that is, `z̄ ^ N exp (-2π b |z|²)` if `N ≥ 0` and `z ^ (-N) exp (-2π b |z|²)` if `N < 0`.
- `complexCharFun N t z = (z / |z|) ^ N * |z| ^ (2 t)`, for `N : ℤ`, `t : ℂ`, `z : ℂ` (an integer
  power in `ℂ`; `|z|` is `‖z‖` coerced to `ℂ`).

## Main results

Integrability. Let `E` be a nontrivial finite-dimensional real normed space with Borel
σ-algebra and `μ` an additive Haar measure on `E`.

- `integrable_norm_pow_mul_exp_neg_mul_sq`: for `c > 0` and `k : ℕ`,
  `x ↦ ‖x‖ ^ k * exp (-c ‖x‖²)` is `μ`-integrable.
- `integrable_of_norm_le_pow_mul_exp`: an a.e.-strongly measurable `f` with
  `‖f x‖ ≤ C ‖x‖ ^ k exp (-c ‖x‖²)` for all `x` (and `c > 0`) is `μ`-integrable.

Complex powers and Gaussian Mellin transforms.

- `ofReal_cpow_eq_exp`: for `x > 0`, `(x : ℂ) ^ z = exp (log x * z)`.
- `ofReal_rpow_cpow`: for `x > 0` and real `r`, `((x ^ r : ℝ) : ℂ) ^ z = (x : ℂ) ^ (r z)`.
- `integral_Ioi_cpow_mul_exp_neg_mul_sq`: for `Re w > 0` and `c > 0`,
  `∫_{(0,∞)} y ^ (w - 1) exp (-(c y²)) dy = (1/2) * ((1/c) ^ (w/2) * Γ(w/2))`.
- `integral_norm_cpow_mul_exp_neg_mul_sq`: for `μ` as above, `n = finrank ℝ E`, `Re w > 0` and
  `c > 0`,
  `∫ ‖x‖ ^ (w - n) exp (-(c ‖x‖²)) dμ = (n μ(B(0,1)) / 2) * ((1/c) ^ (w/2) * Γ(w/2))`, where
  `μ(B(0,1))` is the real-valued measure of the open unit ball.

Real place. Let `a ≠ 0` be real and `y` real.

- `integral_realGaussian_zero_mul_fourierChar`:
  `∫ realGaussian |a| 0 x * 𝐞 (a x y) dx = (√|a|)⁻¹ * realGaussian |a| 0 y`.
- `realGaussian_mul_fourierChar` (auxiliary, any real `a`): the integrand
  `realGaussian |a| p x * 𝐞 (a x y)` equals `x ^ p * exp (-(π |a|) x² + (2π a y i) x + 0)`.
- `integral_realGaussian_one_mul_fourierChar`:
  `∫ realGaussian |a| 1 x * 𝐞 (a x y) dx = (√|a|)⁻¹ * (i * (a/|a|)) * realGaussian |a| 1 y`.
- `integral_realGaussian_mul_realCharFun`: for `b > 0`, `p : ℕ`, `t, s : ℂ` with
  `Re (s + t + p) > 0`,
  `∫ realGaussian b p x * realCharFun p t x * |x| ^ (s - 1) dx = b ^ (-(s + t + p)/2) * Γ_ℝ(s + t + p)`.

Complex place. Let `b > 0` and `u : ℂ`.

- `cGauss_eq`: `cGauss b z = exp (-(2π b |z|²))`; `norm_cGauss`:
  `‖cGauss b z‖ = exp (-(2π b) |z|²)`; `conj_cGauss`: `cGauss b z` is real (equal to its
  conjugate); `continuous_cGauss`.
- `cChar_eq`: `cChar u z = 𝐞 (2 Re (u z))`; `norm_cChar`: `‖cChar u z‖ = 1`;
  `conj_cChar`: `conj (cChar u z) = cChar (-u) z`; `continuous_cChar`.
- `integrable_monomial_mul_cGauss`: for `k, l : ℕ` and continuous `h : ℂ → ℂ` with `‖h z‖ = 1`,
  `z ↦ z ^ k z̄ ^ l cGauss b z h z` is integrable.
- `hasLineDerivAt_of_comp_ofReal` (auxiliary): if `f (z + t v) = Φ t` for all real `t` and
  `Φ : ℂ → ℂ` has complex derivative `f'` at `0`, then `f` has line derivative `f'` at `z` in
  direction `v` (over `ℝ`).
- `integral_mul_lineDeriv_eq_neg` (auxiliary): integration by parts along a real direction `v`
  for products of functions `ℂ → ℂ`: if `f, g` have line derivatives `f' z, g' z` in direction
  `v` at every `z` and `f' g`, `f g'`, `f g` are integrable, then `∫ f g' = -∫ f' g`.
- `hasLineDerivAt_conj_pow_mul_cGauss`, `hasLineDerivAt_cChar`: the line derivatives in
  direction `v` of `z ↦ z̄ ^ n cGauss b z`, namely
  `n z̄^{n-1} v̄ cGauss b z + z̄ ^ n cGauss b z (-(2π b)) (v z̄ + z v̄)`, and of `cChar u`, namely
  `cChar u z * (2π i (u v + ū v̄))`.
- `integral_sub_const_mul_eq_zero` (auxiliary): if `F, G` are integrable with integral `0`,
  then `∫ (F - c G) = 0`.
- `cMoment_zero`: `cMoment b u 0 = (2b)⁻¹ exp (-(2π |u|² / b))`.
- `cMoment_succ`: `cMoment b u (n + 1) = (i u / b) * cMoment b u n`.
- `cMoment_eq`: `cMoment b u n = (i u / b) ^ n * ((2b)⁻¹ exp (-(2π |u|² / b)))`.
- `integral_pow_mul_cGauss_mul_cChar`:
  `∫ z ^ n cGauss b z cChar u z dz = (i ū / b) ^ n * ((2b)⁻¹ exp (-(2π |u|² / b)))`.
- `complexGaussian_eq`: `complexGaussian b N z = z̄ ^ N.toNat z ^ (-N).toNat cGauss b z`.
- `integral_complexGaussian_mul_fourierChar`: for `a ≠ 0` in `ℂ`, `N : ℤ` and `w : ℂ`,
  `∫ complexGaussian |a| N z * 𝐞 (2 Re (a z w)) dz = (2|a|)⁻¹ * (i ^ |N| * (a/|a|) ^ N) * complexGaussian |a| (-N) w`.
- `complexGaussian_mul_complexCharFun`: for `z ≠ 0`,
  `complexGaussian b N z * complexCharFun N t z = |z| ^ (|N| + 2t) * exp (-(2π b |z|²))`
  (any real `b`).
- `integral_complexGaussian_mul_complexCharFun`: for `N : ℤ`, `t, s : ℂ` with
  `Re (s + t + |N|/2) > 0`, writing `w = s + t + |N|/2`,
  `∫ complexGaussian b N z * complexCharFun N t z * |z| ^ (2(s - 1)) dz = (π/2) * b ^ (-w) * Γ_ℂ(w)`.

Here `|N|` is `N.natAbs`, and `|a|`, `|z|` for complex numbers are their absolute values.

## Implemented proof

**Integrability.** `integral_fun_norm_addHaar`'s companion `integrable_fun_norm_addHaar` reduces
integrability of `x ↦ ‖x‖^k exp(-c‖x‖²)` on `E` to integrability of
`y ↦ y^{n-1+k} exp(-c y²)` on `(0, ∞)`, which is `integrableOn_rpow_mul_exp_neg_mul_sq`. The
domination version is `Integrable.mono'`.

**Gaussian Mellin transform on `(0, ∞)`.** Mathlib's `integral_cpow_mul_exp_neg_mul_Ioi` gives
`∫_{(0,∞)} y^{w/2-1} exp(-c y) dy = (1/c)^{w/2} Γ(w/2)`. The substitution `y = x²`
(`integral_comp_rpow_Ioi_of_pos` with exponent 2) turns the left side into
`∫_{(0,∞)} 2x · x^{w-2} exp(-c x²) dx`, using `(x²)^{w/2-1} = x^{w-2}` for `x > 0`
(`ofReal_rpow_cpow`); dividing by 2 gives the claim.

**Radial Mellin transform.** `integral_fun_norm_addHaar` writes
`∫ g(‖x‖) dμ = dim E · μ(B(0,1)) · ∫_{(0,∞)} y^{n-1} g(y) dy`; for
`g(y) = y^{w-n} exp(-c y²)` the integrand is `y^{w-1} exp(-c y²)` (combining powers with
`cpow_add` for `y > 0`), and the previous lemma applies.

**Real Fourier transforms.** For `p = 0` the integrand is `exp(-(π|a|) x² + (2π a y i) x)` and
Mathlib's `integral_cexp_quadratic` gives `(π/(π|a|))^{1/2} exp(-(2π a y i)²/(4 · (-π|a|)))`,
which simplifies to `|a|^{-1/2} exp(-π |a| y²)` using `a² = |a|²` and `i² = -1`. For `p = 1`, let
`q(x) = exp(B x² + C x)` with `B = -π|a|`, `C = 2π a y i`. Then `q' = q · (2Bx + C)` is
integrable and `q` is integrable, so `∫ q' = 0`
(`integral_eq_zero_of_hasDerivAt_of_integrable`), i.e.
`2B ∫ x q(x) dx + C ∫ q = 0`; hence `∫ x q(x) dx = -(C/(2B)) ∫ q = i (a/|a|) y ∫ q`, and the
`p = 0` result finishes.

**Real zeta integral.** For `x ≠ 0` (a.e.), `x^p (x/|x|)^p = |x|^p`, so the integrand equals
`|x|^{s+t+p-1} exp(-(π b)|x|²)`. The radial Mellin formula on `E = ℝ` (dimension 1,
`volume(B(0,1)) = 2`) gives `(πb)^{-(s+t+p)/2} Γ((s+t+p)/2)`, and splitting
`(πb)^{-w/2} = π^{-w/2} b^{-w/2}` (`mul_cpow_ofReal_nonneg`) gives `b^{-w/2} Γ_ℝ(w)`.

**Complex moments.** `cMoment b u 0` is the Gaussian integral
`∫ exp(-(2πb)|z|² + 4π i ⟪ū, z⟫_ℝ) dz` (since `u z + ū z̄ = 2 Re(u z) = 2⟪ū, z⟫_ℝ`), which
`GaussianFourier.integral_cexp_neg_mul_sq_norm_add` evaluates as
`(π/(2πb)) exp((4πi)² |u|²/(4 · 2πb)) = (2b)⁻¹ exp(-2π|u|²/b)`, since `(4πi)² = -16π²`.
For the recursion, integrate by parts along a real direction `v`
(`integral_mul_lineDeriv_eq_neg`) with `f = z̄^n cGauss b`, `g = cChar u`: since
`∫ (f g)' = 0`, one gets
`∫ [n z̄^{n-1} v̄ - 2πb z̄^n (v z̄ + z v̄) + 2π i (u v + ū v̄) z̄^n] cGauss b cChar u = 0`.
(All integrands are integrable by `integrable_monomial_mul_cGauss`.) Taking the identity for
`v = 1` and subtracting `i` times the identity for `v = i` cancels the terms in `v̄`
(including the `n z̄^{n-1}` term and the term in `z`), leaving
`∫ [4π i u z̄^n - 4π b z̄^{n+1}] cGauss b cChar u = 0`, i.e.
`b · cMoment (n+1) = i u · cMoment n`. Induction gives `cMoment_eq`. The integral with `z^n` is
the complex conjugate of `cMoment b (-u) n` (`integral_conj`, `conj_cGauss`, `conj_cChar`).

**Complex Fourier transform.** With `b = |a|`, the character is `𝐞(2 Re(a z w)) = cChar (a w) z`
and `exp(-2π |a w|²/|a|) = cGauss |a| w`. For `N = n ≥ 0`, `cMoment_eq` with `u = a w` gives
`(i a w / |a|)^n (2|a|)⁻¹ cGauss |a| w = (2|a|)⁻¹ i^n (a/|a|)^n w^n cGauss |a| w`, and
`w^n cGauss |a| w = complexGaussian |a| (-n) w`. For `N = -n < 0`,
`integral_pow_mul_cGauss_mul_cChar` gives
`(i conj(a w)/|a|)^n (2|a|)⁻¹ cGauss |a| w`, and `conj a/|a| = (a/|a|)⁻¹`, so this is
`(2|a|)⁻¹ i^n (a/|a|)^{-n} w̄^n cGauss |a| w`.

**Complex zeta integral.** For `z ≠ 0`, `z̄^{N⁺} z^{N⁻} (z/|z|)^N = |z|^{|N|}` (using
`z z̄ = |z|²`), so the integrand equals `|z|^{2w-2} exp(-(2πb)|z|²)` with `w = s + t + |N|/2`.
The radial Mellin formula on `E = ℂ` (dimension 2, `volume(B(0,1)) = π`) with exponent `2w`
gives `π (2πb)^{-w} Γ(w)`, and `(2πb)^{-w} = (2π)^{-w} b^{-w}` gives
`(π/2) b^{-w} · 2(2π)^{-w} Γ(w) = (π/2) b^{-w} Γ_ℂ(w)`.

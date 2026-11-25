# Sine-power kernels along block rotations

Lean module: `Langlands.Representation.Archimedean.RealSwapLandingKernel`, namespace
`Langlands.Archimedean.RealSwapLandingKernel`.

## Role and provenance

This module is an internal step in the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement`. It supplies the
analytic multipliers used to prove the hypothesis `SpecialLanding` of the module
`RealSwapLandingAlgebra`. In that proof the multipliers come from integral operators
`F ↦ ∫₀^π sin^r θ F(r_p(θ) g) dθ`. Such an operator multiplies the `k`-th Fourier mode along
the block rotation `r_p` by the number `ĉ_r(k) = ∫₀^π sin^r θ e^{ikθ} dθ`. This module proves
that fact, together with the recurrence and the symmetry of `ĉ_r`. Then `ĉ_r` is a solution of
the Library predicates `IsRecurrent (r + 2) ε` and `IsSymmetric`.

The integrals and the recurrence are standard calculus. The module formalizes no literature
statement, so it has no sources. All declarations are auxiliary lemmas proved here from
Mathlib and Library results.

## Notation

- `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`. `O(N)` is the subgroup `unitaryCompact ℝ N`.
- `r_p(θ) = blockRotation N p θ` is the rotation in the coordinates `p, p + 1`
  (`RealBlockRotation`).
- `Φ^p_k F (g) = blockFourierCoefficient N p k F g = ∫₀^{2π} F(r_p(θ) g) e^{-ikθ} dθ`
  (`RealBlockFourierFinite`). The integral has no factor `1/(2π)`.
- `IsRecurrent δ ε μ` means `μ(k + 2)(δ + k) = (k + 2 - δ) μ(k)` for all `k ≡ ε (mod 2)`.
  `IsSymmetric ε σ μ` means `μ(-k) = σ μ(k)` for all `k ≡ ε (mod 2)`. Both are Library
  predicates of `RealBlockMultiplier`.

## Declarations

### The coefficients `ĉ_r(k)`

- `kernelIntegrand r k θ = sin^r θ · e^{ikθ}` (a complex number), and
  `sinKernel r k = ĉ_r(k) = ∫₀^π sin^r θ e^{ikθ} dθ` (interval integral).
- `continuous_kernelIntegrand`: the integrand is continuous in `θ`.
- `hasDerivAt_sinPow_exp`: the derivative of `sin^{r+1} θ e^{i(k+1)θ}` is
  `((r + 2 + k)/2) sin^r θ e^{i(k+2)θ} + ((r - k)/2) sin^r θ e^{ikθ}`. Proof: the product and
  chain rules give `(r+1) sin^r θ cos θ e^{i(k+1)θ} + i(k+1) sin^{r+1} θ e^{i(k+1)θ}`. Write
  `X = e^{ikθ}`, `e^{iθ} = cos θ + i sin θ`, and compare the two sides with
  `sin² θ + cos² θ = 1` and `i² = -1` (`linear_combination`).
- `sinKernel_rec` (**recurrence**): `ĉ_r(k + 2)(r + 2 + k) = (k - r) ĉ_r(k)`. Proof: integrate
  the derivative of `hasDerivAt_sinPow_exp` over `[0, π]` (fundamental theorem of calculus).
  The boundary terms vanish because `sin 0 = sin π = 0` and `r + 1 ≥ 1`.
- `exp_neg_int_mul_pi`: `e^{-ikπ} = (-1)^k` for an integer `k`.
- `sinKernel_neg` (**symmetry**): `ĉ_r(-k) = (-1)^k ĉ_r(k)`. Proof: substitute
  `θ ↦ π - θ`. Then `sin(π - θ) = sin θ` and `e^{-ik(π - θ)} = (-1)^k e^{ikθ}`.
- `neg_one_zpow_of_even`: if `k - e` is even then `(-1)^k = (-1)^e`.
- `isSymmetric_sinKernel r e`: `IsSymmetric e ((-1)^e) ĉ_r`, from `sinKernel_neg` and the
  previous lemma.
- `isRecurrent_sinKernel r ε`: `IsRecurrent (r + 2) ε ĉ_r`. This is `sinKernel_rec`, since
  `(k + 2) - (r + 2) = k - r`. It holds for every `k`, so for every parity `ε`.
- `sinKernel_zero_eq`: `ĉ_r(0)` is the real number `∫₀^π sin^r θ dθ`.
- `sinKernel_zero_ne_zero`: `ĉ_r(0) ≠ 0`, because `∫₀^π sin^r θ dθ > 0` (Mathlib's
  `integral_sin_pow_pos`).
- `sinKernel_one_im`: the imaginary part of `ĉ_r(1)` is `∫₀^π sin^{r+1} θ dθ`. Proof: the
  imaginary part commutes with the integral, and `Im(sin^r θ (cos θ + i sin θ)) = sin^{r+1} θ`.
- `sinKernel_one_ne_zero`: `ĉ_r(1) ≠ 0`, since its imaginary part is
  `∫₀^π sin^{r+1} θ dθ > 0`.

### The operators `C^r_p`

- `kernelOp N p r F g = C^r_p F (g) = ∫₀^π sin^r θ F(r_p(θ) g) dθ` for
  `F : GL_N(ℝ) → ℂ`.
- `continuous_kernelOp`: if `F` is continuous, so is `C^r_p F`. Proof: Mathlib's continuity of
  parametric interval integrals of a jointly continuous integrand
  (`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`).
- `kernelOp_congr`: if `F₁` and `F₂` agree on `O(N)`, then `C^r_p F₁` and `C^r_p F₂` agree on
  `O(N)`. The reason is that `r_p(θ) g ∈ O(N)` when `g ∈ O(N)`.
- `integrableOn_uIoc_prod`: a jointly continuous function of two real variables is integrable
  on a product of two intervals `uIoc a b ×ˢ uIoc c d`, because it is integrable on the
  compact product of the closed intervals.
- `blockFourierCoefficient_kernelOp` (**multiplier formula**): for `p + 1 < N`, a continuous
  `F`, every `k ∈ ℤ` and every `g` (not only `g ∈ O(N)`),
  `Φ^p_k (C^r_p F)(g) = ĉ_r(k) Φ^p_k F (g)`. Proof: exchange the two interval integrals with
  Fubini (`intervalIntegral_intervalIntegral_swap`, using the previous lemma). For fixed
  `φ ∈ [0, π]`, `r_p(φ) r_p(θ) = r_p(θ) r_p(φ)`, so the inner integral is
  `Φ^p_k F (r_p(φ) g) = e^{ikφ} Φ^p_k F (g)` (the Library lemma
  `blockFourierCoefficient_blockRotation_mul`). The outer integral is then
  `∫₀^π sin^r φ e^{ikφ} dφ · Φ^p_k F (g) = ĉ_r(k) Φ^p_k F (g)`.

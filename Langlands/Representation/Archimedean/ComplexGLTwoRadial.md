# The radial integrals `∫_ℂ (1 + |z|²)^β |z|^(2k) dz`

Module `Langlands.Representation.Archimedean.ComplexGLTwoRadial`, namespace
`Langlands.Archimedean.ComplexGLTwoNoncompact`. Internal helper module for the proof of
`ComplexGLTwoMomentCompletenessStatement` (see `ComplexGLTwoMomentCompletenessProof`). It
contains elementary integral computations; no statement is quoted from the literature.
Notation `pw σ z = (1 + |z|²)^σ` and `W z = 1 + z z̄` as in `ComplexGLTwoWirtinger`. Integrals
are over `ℂ` with Lebesgue measure (`volume`).

## Definitions

* `rad β k z = (1 + |z|²)^β (z z̄)^k`.
* `radInt β k = I(β, k) = ∫_ℂ (1 + |z|²)^β (z z̄)^k dz` (Bochner integral; it is only used
  where the integrand is integrable).

## Results

* `norm_pw`: `|pw σ z| = (1 + |z|²)^(Re σ)`.
* `pw_natCast`: `pw k = W^k` for `k ∈ ℕ`.
* `continuous_pw'`, `continuous_rad`: continuity of `pw σ` and `rad β k`.
* `integrable_pw`: if `Re σ < -1`, then `pw σ` is integrable.
* `norm_rad_le`: `|rad β k z| ≤ |pw (β + k) z|`.
* `integrable_rad`: if `Re β + k < -1`, then `rad β k` is integrable.
* `rad_succ`, `radInt_succ`: `rad β (k + 1) = rad (β + 1) k - rad β k`, and, if
  `Re β + (k + 1) < -1`, `I(β, k + 1) = I(β + 1, k) - I(β, k)`.
* `radInt_zero`: if `Re β < -1`, then `I(β, 0) = π / (-(β + 1))`.
* `radInt_mul_prod`: if `Re β + k < -1`, then
  `I(β, k) ∏_{j=0}^{k} (-(β + j + 1)) = π k!`.
* `radInt_ne_zero`: if `Re β + k < -1`, then `I(β, k) ≠ 0`.

## Proofs

* `norm_pw`: `|exp(σ log(1 + |z|²))| = exp(Re σ · log(1 + |z|²))`, which is the real power.
* `integrable_pw`: by `norm_pw`, `|pw σ z| = (1 + |z|²)^(-(-2 Re σ)/2)`, and Mathlib's
  `integrable_rpow_neg_one_add_norm_sq` gives integrability of `(1 + |z|²)^(-r/2)` on the
  real 2-dimensional space `ℂ` when `2 < r`; here `r = -2 Re σ > 2`.
* `norm_rad_le`: `rad β k = pw β · |z|^(2k)` and `pw (β + k) = pw β · W^k`
  (`pw_add`, `pw_natCast`), and `|z|^2 ≤ 1 + |z|²`.
* `integrable_rad`: dominated by the integrable `|pw (β + k)|` (`norm_rad_le`,
  `integrable_pw`), and continuous, hence measurable.
* `rad_succ`: `z z̄ = W - 1` and `pw (β + 1) = pw β · W` (`pw_add_one`). `radInt_succ`
  integrates this identity; both terms on the right are integrable by `integrable_rad`.
* `radInt_zero`: the Library theorem `ComplexSwapJacquet.integral_one_add_norm_sq_cpow`
  (`∫_ℂ (1 + |z|²)^β dz = π / (-(β + 1))` for `Re β < -1`), after identifying `rad β 0` with the
  integrand there.
* `radInt_mul_prod`: induction on `k`, for all `β` at once. For `k = 0` this is `radInt_zero`
  (`β + 1 ≠ 0` since `Re β < -1`). For `k + 1`, `radInt_succ` writes `I(β, k + 1)` as
  `I(β + 1, k) - I(β, k)`; the product `∏_{j=0}^{k+1} (-(β + j + 1))` is split once as
  `(∏_{j=0}^{k} (-(β + 1 + j + 1))) (-(β + 1))` and once as
  `(∏_{j=0}^{k} (-(β + j + 1))) (-(β + k + 2))`, and the two induction hypotheses (at `β + 1`
  and at `β`) give `π k! (-(β + 1)) - π k! (-(β + k + 2)) = π (k + 1)!`
  (`linear_combination`).
* `radInt_ne_zero`: otherwise the left side of `radInt_mul_prod` would be `0`, but `π ≠ 0` and
  `k! ≠ 0`.

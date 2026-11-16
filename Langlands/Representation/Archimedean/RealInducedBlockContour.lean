import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# A contour bound for the rotation integrals of induced `GL_2(ℝ)` blocks

For `u, w ∈ ℂ` with `|w| < |u|` put `X(θ) = u e^{iθ} + w e^{-iθ}`. For `l, n ∈ ℕ` and `N ∈ ℤ`,

`|∫₀^{2π} X(θ)^l / conj(X(θ))^n · e^{iNθ} dθ| ≤ 2π (1/2)^{n-l+N} ((5/4)|u|)^l / ((3/4)|u|)^n`.

With `z = e^{iθ}` the integrand is `G(z) z^{n-l+N}`, `G(z) = (u z² + w)^l / (ū + w̄ z²)^n`, which
is holomorphic on `0 < |z| ≤ 1` because `|w̄ z²| < |u|` there. So the integral is
`-i ∮_{|z|=1} G(z) z^{n-l+N-1} dz`, and by Cauchy's theorem on the annulus
`1/2 ≤ |z| ≤ 1` the circle `|z| = 1` can be replaced by `|z| = 1/2`, where
`|u z² + w| ≤ (5/4)|u|` and `|ū + w̄ z²| ≥ (3/4)|u|`.

This is the analytic input for the rotation (torus) averages of the `K`-type functions of the
induced (discrete series) blocks of real standard modules: for the `K`-type `j'` function of
`D_m` the integrand along the rotations has exactly this shape, and the bound gives decay
`|u|^{l-n} = |u|^{-(m+1)}`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealInducedBlockContour

open Complex Real MeasureTheory Metric Set

/-- `X(θ) = u e^{iθ} + w e^{-iθ}`. -/
def wave (u w : ℂ) (θ : ℝ) : ℂ :=
  u * cexp (θ * I) + w * cexp (-(θ * I))

/-- The complex conjugate `conj(X(θ)) = ū e^{-iθ} + w̄ e^{iθ}`. -/
theorem conj_wave (u w : ℂ) (θ : ℝ) :
    (starRingEnd ℂ) (wave u w θ) =
      (starRingEnd ℂ) u * cexp (-(θ * I)) + (starRingEnd ℂ) w * cexp (θ * I) := by
  have h1 : (starRingEnd ℂ) (cexp (θ * I)) = cexp (-(θ * I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
  have h2 : (starRingEnd ℂ) (cexp (-(θ * I))) = cexp (θ * I) := by
    rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      neg_neg]
  simp only [wave, map_add, map_mul, h1, h2]

/-- The holomorphic factor `G(z) = (u z² + w)^l / (ū + w̄ z²)^n`. -/
def holo (u w : ℂ) (l n : ℕ) (z : ℂ) : ℂ :=
  (u * z ^ 2 + w) ^ l / ((starRingEnd ℂ) u + (starRingEnd ℂ) w * z ^ 2) ^ n

theorem den_ne_zero {u w : ℂ} (hwu : ‖w‖ < ‖u‖) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (starRingEnd ℂ) u + (starRingEnd ℂ) w * z ^ 2 ≠ 0 := by
  intro h
  have h' : ‖(starRingEnd ℂ) u‖ = ‖(starRingEnd ℂ) w * z ^ 2‖ := by
    rw [eq_neg_of_add_eq_zero_left h, norm_neg]
  rw [norm_mul, norm_pow, Complex.norm_conj, Complex.norm_conj] at h'
  have : ‖w‖ * ‖z‖ ^ 2 ≤ ‖w‖ :=
    mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
  linarith

/-- The integrand on the unit circle in terms of `G`. -/
theorem integrand_eq (u w : ℂ) (l n : ℕ) (N : ℤ) (θ : ℝ) :
    wave u w θ ^ l / ((starRingEnd ℂ) (wave u w θ)) ^ n * cexp (N * θ * I) =
      holo u w l n (cexp (θ * I)) * cexp (θ * I) ^ ((n : ℤ) - l + N) := by
  set z := cexp (θ * I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hinv : cexp (-(θ * I)) = z⁻¹ := by rw [Complex.exp_neg]
  have hN : cexp (N * θ * I) = z ^ N := by
    rw [mul_assoc, Complex.exp_int_mul]
  rw [conj_wave, hN]
  simp only [wave, holo, hinv]
  have e1 : u * z + w * z⁻¹ = (u * z ^ 2 + w) * z⁻¹ := by field_simp
  have e2 : (starRingEnd ℂ) u * z⁻¹ + (starRingEnd ℂ) w * z =
      ((starRingEnd ℂ) u + (starRingEnd ℂ) w * z ^ 2) * z⁻¹ := by field_simp
  rw [e1, e2, mul_pow, mul_pow, zpow_add₀ hz0, zpow_sub₀ hz0, zpow_natCast, zpow_natCast,
    inv_pow, inv_pow]
  field_simp

/-- The circle integral on `|z| = 1` of `G(z) z^{k-1}` is `i` times the rotation integral. -/
theorem circleIntegral_eq (u w : ℂ) (l n : ℕ) (k : ℤ) :
    (∮ z in C(0, 1), holo u w l n z * z ^ (k - 1)) =
      I * ∫ θ in (0 : ℝ)..2 * π, holo u w l n (cexp (θ * I)) * cexp (θ * I) ^ k := by
  rw [circleIntegral, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap, circleMap_zero, Complex.ofReal_one, one_mul, smul_eq_mul]
  have hz0 : cexp (θ * I) ≠ 0 := Complex.exp_ne_zero _
  rw [zpow_sub_one₀ hz0]
  field_simp

theorem norm_holo_le {u w : ℂ} (hwu : ‖w‖ < ‖u‖) (l n : ℕ) {z : ℂ} (hz : ‖z‖ = 1 / 2) :
    ‖holo u w l n z‖ ≤ ((5 / 4) * ‖u‖) ^ l / ((3 / 4) * ‖u‖) ^ n := by
  have hz2 : ‖z‖ ^ 2 = 1 / 4 := by rw [hz]; norm_num
  have hnum : ‖u * z ^ 2 + w‖ ≤ (5 / 4) * ‖u‖ := by
    calc ‖u * z ^ 2 + w‖ ≤ ‖u * z ^ 2‖ + ‖w‖ := norm_add_le _ _
      _ = ‖u‖ / 4 + ‖w‖ := by rw [norm_mul, norm_pow, hz2]; ring
      _ ≤ (5 / 4) * ‖u‖ := by linarith
  have hden : (3 / 4) * ‖u‖ ≤ ‖(starRingEnd ℂ) u + (starRingEnd ℂ) w * z ^ 2‖ := by
    have h := norm_sub_norm_le ((starRingEnd ℂ) u) (-((starRingEnd ℂ) w * z ^ 2))
    rw [sub_neg_eq_add, norm_neg, norm_mul, norm_pow, hz2, Complex.norm_conj,
      Complex.norm_conj] at h
    linarith
  have hu0 : 0 < ‖u‖ := lt_of_le_of_lt (norm_nonneg _) hwu
  rw [holo, norm_div, norm_pow, norm_pow]
  exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hnum l)
    (by positivity) (pow_le_pow_left₀ (by positivity) hden n)

/-- **Contour bound.** For `|w| < |u|`:
`|∫₀^{2π} X(θ)^l / conj(X(θ))^n e^{iNθ} dθ| ≤ 2π (1/2)^{n-l+N} ((5/4)|u|)^l / ((3/4)|u|)^n`,
where `X(θ) = u e^{iθ} + w e^{-iθ}`. -/
theorem norm_integral_le {u w : ℂ} (hwu : ‖w‖ < ‖u‖) (l n : ℕ) (N : ℤ) :
    ‖∫ θ in (0 : ℝ)..2 * π,
        wave u w θ ^ l / ((starRingEnd ℂ) (wave u w θ)) ^ n * cexp (N * θ * I)‖ ≤
      2 * π * (1 / 2 : ℝ) ^ ((n : ℤ) - l + N) *
        (((5 / 4) * ‖u‖) ^ l / ((3 / 4) * ‖u‖) ^ n) := by
  set k : ℤ := (n : ℤ) - l + N
  set f : ℂ → ℂ := fun z => holo u w l n z * z ^ (k - 1)
  have hcont : ContinuousOn f (closedBall (0 : ℂ) 1 \ ball 0 (1 / 2)) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz.1
    have hz0 : z ≠ 0 := by
      intro h
      apply hz.2
      simp [h]
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.div (by fun_prop) (by fun_prop)
      exact pow_ne_zero _ (den_ne_zero hwu hz1)
    · exact continuousAt_zpow₀ _ _ (Or.inl hz0)
  have hdiff : ∀ z ∈ (ball (0 : ℂ) 1 \ closedBall 0 (1 / 2)) \ (∅ : Set ℂ),
      DifferentiableAt ℂ f z := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by
      have := hz.1.1
      rw [mem_ball_zero_iff] at this
      exact this.le
    have hz0 : z ≠ 0 := by
      intro h
      apply hz.1.2
      simp [h]
    apply DifferentiableAt.mul
    · apply DifferentiableAt.div (by fun_prop) (by fun_prop)
      exact pow_ne_zero _ (den_ne_zero hwu hz1)
    · exact differentiableAt_zpow.2 (Or.inl hz0)
  have hshift := circleIntegral_eq_of_differentiable_on_annulus_off_countable
    (c := (0 : ℂ)) (r := 1 / 2) (R := 1) (by norm_num) (by norm_num) countable_empty hcont hdiff
  have hbound : ∀ z ∈ sphere (0 : ℂ) (1 / 2),
      ‖f z‖ ≤ ((5 / 4) * ‖u‖) ^ l / ((3 / 4) * ‖u‖) ^ n * (1 / 2 : ℝ) ^ (k - 1) := by
    intro z hz
    have hz' : ‖z‖ = 1 / 2 := by simpa using hz
    simp only [f, norm_mul, Complex.norm_zpow, hz']
    exact mul_le_mul_of_nonneg_right (norm_holo_le hwu l n hz') (by positivity)
  have hle := circleIntegral.norm_integral_le_of_norm_le_const (by norm_num) hbound
  have hI : ‖∫ θ in (0 : ℝ)..2 * π,
      wave u w θ ^ l / ((starRingEnd ℂ) (wave u w θ)) ^ n * cexp (N * θ * I)‖ =
      ‖∮ z in C(0, 1), f z‖ := by
    rw [circleIntegral_eq, norm_mul, Complex.norm_I, one_mul]
    congr 1
    exact intervalIntegral.integral_congr fun θ _ => integrand_eq u w l n N θ
  rw [hI, hshift]
  refine hle.trans (le_of_eq ?_)
  rw [zpow_sub_one₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  field_simp

end RealInducedBlockContour

end Langlands.Archimedean

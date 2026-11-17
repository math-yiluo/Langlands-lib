import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fourier coefficients of `θ ↦ (P e^{iθ} + Q e^{-iθ})^{-N}`

If `‖P‖ ≠ ‖Q‖`, the function `θ ↦ (P e^{iθ} + Q e^{-iθ})^{-N}` has no Fourier modes `e^{ikθ}`
with `|k| < N`. For `‖P‖ < ‖Q‖` the coefficient of `e^{ikθ}` is a circle integral of the
holomorphic function `w ↦ w^(N-k-1) (P w² + Q)^{-N}` on a neighbourhood of the closed unit disc,
hence zero by Cauchy's theorem when `k < N`. The case `‖Q‖ < ‖P‖` follows by `θ ↦ -θ`.
-/

noncomputable section

namespace Langlands.Analysis.InversePowerFourier

open Complex MeasureTheory Set

/-- The integrand: `(P e^{iθ} + Q e^{-iθ})^{-N} e^{-ikθ}`. -/
def integrand (P Q : ℂ) (N : ℕ) (k : ℤ) (θ : ℝ) : ℂ :=
  ((P * exp (θ * I) + Q * exp (-(θ * I))) ^ N)⁻¹ * exp (-((k : ℂ) * θ * I))

theorem integrand_neg (P Q : ℂ) (N : ℕ) (k : ℤ) (θ : ℝ) :
    integrand P Q N k (-θ) = integrand Q P N (-k) θ := by
  unfold integrand
  push_cast
  congr 2
  · ring_nf
  · ring_nf

theorem integrand_periodic (P Q : ℂ) (N : ℕ) (k : ℤ) :
    Function.Periodic (integrand P Q N k) (2 * Real.pi) := by
  intro θ
  unfold integrand
  have h1 : exp (((θ + 2 * Real.pi : ℝ) : ℂ) * I) = exp ((θ : ℂ) * I) := by
    rw [show ((θ + 2 * Real.pi : ℝ) : ℂ) * I = (θ : ℂ) * I + 2 * Real.pi * I by push_cast; ring,
      exp_add, exp_two_pi_mul_I, mul_one]
  have h2 : exp (-(((θ + 2 * Real.pi : ℝ) : ℂ) * I)) = exp (-((θ : ℂ) * I)) := by
    rw [show -(((θ + 2 * Real.pi : ℝ) : ℂ) * I) = -((θ : ℂ) * I) + (-1 : ℤ) * (2 * Real.pi * I) by
      push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  have h3 : exp (-((k : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) * I)) = exp (-((k : ℂ) * θ * I)) := by
    rw [show -((k : ℂ) * ((θ + 2 * Real.pi : ℝ) : ℂ) * I) =
        -((k : ℂ) * θ * I) + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, h2, h3]

/-- The holomorphic function whose circle integral computes the coefficient. -/
def kernel (P Q : ℂ) (N : ℕ) (m : ℕ) (w : ℂ) : ℂ := w ^ m * ((P * w ^ 2 + Q) ^ N)⁻¹

theorem circleIntegral_kernel_eq_zero {P Q : ℂ} (hPQ : ‖P‖ < ‖Q‖) (N m : ℕ) :
    (∮ w in C(0, 1), kernel P Q N m w) = 0 := by
  apply DiffContOnCl.circleIntegral_eq_zero zero_le_one
  have hne : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, P * w ^ 2 + Q ≠ 0 := by
    intro w hw h0
    have hw1 : ‖w‖ ≤ 1 := by simpa using hw
    have : ‖P * w ^ 2‖ = ‖Q‖ := by rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
    rw [norm_mul, norm_pow] at this
    have : ‖P‖ * ‖w‖ ^ 2 ≤ ‖P‖ := by
      calc ‖P‖ * ‖w‖ ^ 2 ≤ ‖P‖ * 1 := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) hw1
        _ = ‖P‖ := mul_one _
    linarith
  have hd : DifferentiableOn ℂ (kernel P Q N m) (Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    unfold kernel
    apply DifferentiableAt.mul (by fun_prop)
    exact DifferentiableAt.inv (by fun_prop) (pow_ne_zero _ (hne w hw))
  exact hd.diffContOnCl_ball subset_rfl

/-- **Case `‖P‖ < ‖Q‖`**: the coefficients of `e^{ikθ}` with `k < N` vanish. -/
theorem integral_integrand_eq_zero_of_lt {P Q : ℂ} (hPQ : ‖P‖ < ‖Q‖) (N : ℕ) {k : ℤ}
    (hk : k < N) : ∫ θ in (0 : ℝ)..2 * Real.pi, integrand P Q N k θ = 0 := by
  set m : ℕ := ((N : ℤ) - k - 1).toNat with hm
  have hmk : ((m : ℕ) : ℤ) + 1 = (N : ℤ) - k := by
    rw [hm, Int.toNat_of_nonneg (by omega)]
    ring
  have h := circleIntegral_kernel_eq_zero hPQ N m
  rw [circleIntegral] at h
  have heq : ∀ θ : ℝ, deriv (circleMap 0 1) θ • kernel P Q N m (circleMap 0 1 θ) =
      I * integrand P Q N k θ := by
    intro θ
    rw [deriv_circleMap, circleMap_zero, smul_eq_mul]
    unfold kernel integrand
    set u : ℂ := exp ((θ : ℂ) * I) with hu
    have hu0 : u ≠ 0 := exp_ne_zero _
    have hinv : exp (-((θ : ℂ) * I)) = u⁻¹ := by rw [hu, exp_neg]
    have hk' : exp (-((k : ℂ) * θ * I)) = u ^ (-k) := by
      rw [hu, ← exp_int_mul]
      congr 1
      push_cast
      ring
    rw [hinv, hk']
    simp only [Complex.ofReal_one, one_mul]
    have hsum : P * u + Q * u⁻¹ = u⁻¹ * (P * u ^ 2 + Q) := by
      field_simp
    rw [hsum, mul_pow, mul_inv, inv_pow, inv_inv]
    have hz : u ^ (-k) = u ^ (m + 1) * (u ^ N)⁻¹ := by
      rw [← zpow_natCast u N, ← zpow_neg, ← zpow_natCast u (m + 1), ← zpow_add₀ hu0]
      congr 1
      push_cast
      omega
    rw [hz]
    field_simp
    ring
  simp only [heq] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact (mul_eq_zero.mp h).resolve_left I_ne_zero

/-- **Case `‖Q‖ < ‖P‖`**: the coefficients of `e^{ikθ}` with `-N < k` vanish. -/
theorem integral_integrand_eq_zero_of_gt {P Q : ℂ} (hQP : ‖Q‖ < ‖P‖) (N : ℕ) {k : ℤ}
    (hk : -(N : ℤ) < k) : ∫ θ in (0 : ℝ)..2 * Real.pi, integrand P Q N k θ = 0 := by
  have h := integral_integrand_eq_zero_of_lt hQP N (k := -k) (by omega)
  have hneg : ∫ θ in (0 : ℝ)..2 * Real.pi, integrand Q P N (-k) θ =
      ∫ θ in (0 : ℝ)..2 * Real.pi, integrand P Q N k (-θ) := by
    simp only [integrand_neg]
  rw [hneg, intervalIntegral.integral_comp_neg] at h
  rw [← h]
  have hp := (integrand_periodic P Q N k).intervalIntegral_add_eq (-(2 * Real.pi)) 0
  simp only [zero_add, neg_add_cancel] at hp
  rw [neg_zero]
  exact hp.symm

/-- **The Fourier vanishing**: if `‖P‖ ≠ ‖Q‖`, the coefficients of
`θ ↦ (P e^{iθ} + Q e^{-iθ})^{-N}` at all `e^{ikθ}` with `|k| < N` vanish. -/
theorem integral_integrand_eq_zero {P Q : ℂ} (hPQ : ‖P‖ ≠ ‖Q‖) (N : ℕ) {k : ℤ}
    (hk : |k| < N) : ∫ θ in (0 : ℝ)..2 * Real.pi, integrand P Q N k θ = 0 := by
  rcases lt_or_gt_of_ne hPQ with h | h
  · exact integral_integrand_eq_zero_of_lt h N (lt_of_le_of_lt (le_abs_self k) hk)
  · exact integral_integrand_eq_zero_of_gt h N (by
      have := neg_abs_le k
      omega)

/-- If `‖P‖ ≠ ‖Q‖`, then `P e^{iθ} + Q e^{-iθ}` never vanishes and the integrand is continuous. -/
theorem continuous_integrand {P Q : ℂ} (hPQ : ‖P‖ ≠ ‖Q‖) (N : ℕ) (k : ℤ) :
    Continuous (integrand P Q N k) := by
  have hne : ∀ θ : ℝ, P * exp (θ * I) + Q * exp (-(θ * I)) ≠ 0 := by
    intro θ h0
    apply hPQ
    have h1 : ‖P * exp (θ * I)‖ = ‖Q * exp (-(θ * I))‖ := by
      rw [eq_neg_of_add_eq_zero_left h0, norm_neg]
    rwa [norm_mul, norm_mul, norm_exp_ofReal_mul_I,
      show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I,
      mul_one, mul_one] at h1
  unfold integrand
  refine Continuous.mul (Continuous.inv₀ ?_ fun θ => pow_ne_zero _ (hne θ)) ?_
  · fun_prop
  · fun_prop

end Langlands.Analysis.InversePowerFourier

namespace Langlands.Analysis.InversePowerFourier

open Complex

/-! ### The bottom row of a rotated `2 × 2` matrix -/

/-- For `M = [[a, b], [c, d]]`, the first coefficient of `d' - i c'` of `r(θ) M` in
`e^{iθ}`, where `(c', d')` is the bottom row and `r(θ) = [[cos θ, -sin θ], [sin θ, cos θ]]`. -/
def rotP (a b c d : ℝ) : ℂ := (((d - a : ℝ) : ℂ) - I * ((c + b : ℝ) : ℂ)) / 2

/-- The second coefficient, of `e^{-iθ}`. -/
def rotQ (a b c d : ℝ) : ℂ := (((d + a : ℝ) : ℂ) + I * ((b - c : ℝ) : ℂ)) / 2

/-- The bottom row of `r(θ) M` is `(sin θ a + cos θ c, sin θ b + cos θ d)`, and
`d' - i c' = P e^{iθ} + Q e^{-iθ}`. -/
theorem rotated_bottom_eq (a b c d θ : ℝ) :
    ((Real.sin θ * b + Real.cos θ * d : ℝ) : ℂ) - I * ((Real.sin θ * a + Real.cos θ * c : ℝ) : ℂ) =
      rotP a b c d * exp (θ * I) + rotQ a b c d * exp (-(θ * I)) := by
  unfold rotP rotQ
  have hc : Complex.cos (θ : ℂ) = (exp (θ * I) + exp (-(θ * I))) / 2 := by
    have h := Complex.two_cos (θ : ℂ)
    rw [neg_mul] at h
    linear_combination h / 2
  have hs : Complex.sin (θ : ℂ) = (exp (-(θ * I)) - exp (θ * I)) * I / 2 := by
    have h := Complex.two_sin (θ : ℂ)
    rw [neg_mul] at h
    linear_combination h / 2
  push_cast
  rw [hc, hs]
  linear_combination ((a : ℂ) / 2 * (exp (θ * I) - exp (-(θ * I)))) * Complex.I_sq

/-- `‖P‖² - ‖Q‖² = -(a d - b c)`: the two coefficients have different norms when the matrix is
invertible. -/
theorem normSq_rotP_sub_normSq_rotQ (a b c d : ℝ) :
    Complex.normSq (rotP a b c d) - Complex.normSq (rotQ a b c d) = -(a * d - b * c) := by
  unfold rotP rotQ
  simp only [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  ring

theorem norm_rotP_ne_norm_rotQ {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) :
    ‖rotP a b c d‖ ≠ ‖rotQ a b c d‖ := by
  intro h
  have h2 : Complex.normSq (rotP a b c d) = Complex.normSq (rotQ a b c d) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
  have := normSq_rotP_sub_normSq_rotQ a b c d
  rw [h2, sub_self] at this
  exact hdet (by linarith)

end Langlands.Analysis.InversePowerFourier

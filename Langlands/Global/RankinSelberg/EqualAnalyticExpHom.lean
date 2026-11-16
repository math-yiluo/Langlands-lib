import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Continuous exponential functions on the real line

A continuous function `f : ℝ → ℂ` with `f 0 = 1` and `f (x + y) = f x f y` is `x ↦ exp (w x)`
for some `w : ℂ` (`exists_eq_cexp_of_continuous`).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Langlands.Global.RankinSelbergGlobal.EqualAnalytic

/-- **Continuous exponential functions on `ℝ`.** A continuous `f : ℝ → ℂ` with `f 0 = 1` and
`f (x + y) = f x * f y` is `x ↦ exp (w x)`. The proof: `f x ∫₀^δ f = ∫ₓ^(x+δ) f` with
`∫₀^δ f ≠ 0`, so `f` is differentiable with `f' = w f`, and `f x exp (-w x)` is constant. -/
theorem exists_eq_cexp_of_continuous {f : ℝ → ℂ} (hf : Continuous f) (h0 : f 0 = 1)
    (hadd : ∀ x y, f (x + y) = f x * f y) : ∃ w : ℂ, ∀ x : ℝ, f x = Complex.exp (w * x) := by
  obtain ⟨δ, hδ, hc⟩ : ∃ δ : ℝ, 0 < δ ∧ (∫ t in (0 : ℝ)..δ, f t) ≠ 0 := by
    have hcont := hf.continuousAt (x := 0)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hball⟩ := hcont (1 / 2) (by norm_num)
    refine ⟨δ / 2, by positivity, fun h => ?_⟩
    have hle : ‖∫ t in (0 : ℝ)..δ / 2, (f t - 1)‖ ≤ (1 / 2) * |δ / 2 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le (by positivity)] at ht
      have hd : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        linarith [ht.2]
      have := hball hd
      rw [h0, dist_eq_norm] at this
      exact this.le
    have heq : (∫ t in (0 : ℝ)..δ / 2, (f t - 1)) = -((δ / 2 : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const, h,
        intervalIntegral.integral_const]
      simp
    rw [heq, norm_neg, Complex.norm_real, Real.norm_eq_abs, sub_zero,
      abs_of_pos (by positivity : (0 : ℝ) < δ / 2)] at hle
    linarith
  set c := ∫ t in (0 : ℝ)..δ, f t with hcdef
  set G : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, f t with hG
  have hGd : ∀ u, HasDerivAt G (f u) u := fun u => (hf.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hmul : ∀ x, f x * c = G (x + δ) - G x := by
    intro x
    rw [hcdef, ← intervalIntegral.integral_const_mul]
    have h1 : (∫ t in (0 : ℝ)..δ, f x * f t) = ∫ t in (0 : ℝ)..δ, f (x + t) :=
      intervalIntegral.integral_congr fun t _ => (hadd x t).symm
    rw [h1, intervalIntegral.integral_comp_add_left, add_zero, hG]
    exact (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  have hfeq : ∀ x, f x = (G (x + δ) - G x) * c⁻¹ := fun x => by
    rw [← hmul, mul_assoc, mul_inv_cancel₀ hc, mul_one]
  set w : ℂ := (f δ - 1) * c⁻¹ with hw
  have hfd : ∀ x, HasDerivAt f (f x * w) x := by
    intro x
    have h1 : HasDerivAt (fun y => (G (y + δ) - G y) * c⁻¹) ((f (x + δ) - f x) * c⁻¹) x :=
      ((HasDerivAt.comp_add_const x δ (hGd (x + δ))).sub (hGd x)).mul_const c⁻¹
    have h2 : (fun y => (G (y + δ) - G y) * c⁻¹) = f := funext fun y => (hfeq y).symm
    rw [h2] at h1
    convert h1 using 1
    rw [hadd, hw]
    ring
  refine ⟨w, fun x => ?_⟩
  have hed : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-(w * y))) (Complex.exp (-(w * y)) *
      (-(w * 1))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
    have h2 : HasDerivAt (fun y : ℝ => -(w * (y : ℂ))) (-(w * 1)) y := (h1.const_mul w).neg
    exact HasDerivAt.cexp h2
  have hhd : ∀ y, HasDerivAt (fun y : ℝ => f y * Complex.exp (-(w * y))) 0 y := by
    intro y
    convert (hfd y).mul (hed y) using 1
    ring
  have hconst := is_const_of_deriv_eq_zero (f := fun y : ℝ => f y * Complex.exp (-(w * y)))
    (fun y => (hhd y).differentiableAt) (fun y => (hhd y).deriv) x 0
  simp only [h0, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hconst
  have hx : f x = f x * Complex.exp (-(w * x)) * Complex.exp (w * x) := by
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [hx, hconst, one_mul]

end Langlands.Global.RankinSelbergGlobal.EqualAnalytic

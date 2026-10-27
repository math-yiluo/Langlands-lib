import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Langlands.Analysis.MellinHalfPlaneStatement

/-!
# Proof of holomorphy of positive-weight Mellin integrals

This module proves `Langlands.Analysis.MellinHalfPlaneStatement` by dominated
differentiation under the integral sign. Near a point `s₀` of the half-plane,
the derivative is bounded by integrands at the positive real endpoints
`s₀.re ± 2 * h`, where `h = s₀.re / 4` absorbs the logarithm.
-/

namespace Langlands.Analysis

open MeasureTheory Metric Filter

universe u

/-- For `0 < r` and `0 < h`, the logarithm is absorbed by two opposite powers:
`h * |log r| ≤ r ^ h + r ^ (-h)`. -/
private lemma mul_abs_log_le_rpow_add_rpow_neg {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    h * |Real.log r| ≤ r ^ h + r ^ (-h) := by
  have h1 : h * Real.log r ≤ r ^ h := by
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hr h)
    rw [Real.log_rpow hr] at this
    linarith
  have h2 : -(h * Real.log r) ≤ r ^ (-h) := by
    have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hr (-h))
    rw [Real.log_rpow hr] at this
    linarith
  have h3 := (Real.rpow_pos_of_pos hr h).le
  have h4 := (Real.rpow_pos_of_pos hr (-h)).le
  rw [← abs_of_pos hh, ← abs_mul, abs_of_pos hh]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A real power of a positive number at an exponent in `[A, B]` is at most
the sum of the endpoint powers. -/
private lemma rpow_le_rpow_add_rpow {r A B y : ℝ} (hr : 0 < r) (hA : A ≤ y) (hB : y ≤ B) :
    r ^ y ≤ r ^ A + r ^ B := by
  rcases le_total r 1 with h | h
  · have h1 := Real.rpow_le_rpow_of_exponent_ge hr h hA
    have h2 := (Real.rpow_pos_of_pos hr B).le
    linarith
  · have h1 := Real.rpow_le_rpow_of_exponent_le h hB
    have h2 := (Real.rpow_pos_of_pos hr A).le
    linarith

/-- The pointwise derivative estimate: if `A ≤ u - h` and `u + h ≤ B` with
`0 < h`, then `r ^ u * |log r| ≤ 2 / h * (r ^ A + r ^ B)` for `0 < r`. -/
private lemma rpow_mul_abs_log_le {r h u A B : ℝ} (hr : 0 < r) (hh : 0 < h)
    (hA : A ≤ u - h) (hB : u + h ≤ B) :
    r ^ u * |Real.log r| ≤ 2 / h * (r ^ A + r ^ B) := by
  have b1 : r ^ (u + h) ≤ r ^ A + r ^ B :=
    rpow_le_rpow_add_rpow hr (by linarith) hB
  have b2 : r ^ (u + -h) ≤ r ^ A + r ^ B :=
    rpow_le_rpow_add_rpow hr (by linarith) (by linarith)
  have key : h * (r ^ u * |Real.log r|) ≤ 2 * (r ^ A + r ^ B) :=
    calc h * (r ^ u * |Real.log r|) = r ^ u * (h * |Real.log r|) := by ring
      _ ≤ r ^ u * (r ^ h + r ^ (-h)) :=
          mul_le_mul_of_nonneg_left (mul_abs_log_le_rpow_add_rpow_neg hr hh)
            (Real.rpow_pos_of_pos hr u).le
      _ = r ^ (u + h) + r ^ (u + -h) := by
          rw [Real.rpow_add hr, Real.rpow_add hr]; ring
      _ ≤ (r ^ A + r ^ B) + (r ^ A + r ^ B) := add_le_add b1 b2
      _ = 2 * (r ^ A + r ^ B) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hh]
  linarith

/-- Positive real weights and real-axis integrability imply holomorphy of the
actual complex-power Bochner integral on the positive half-plane. -/
theorem mellinHalfPlane : MellinHalfPlaneStatement.{u} := by
  intro X _ μ c d κ hd hc hdm hint
  have hpow_meas : ∀ w : ℂ, AEStronglyMeasurable (fun x => (d x : ℂ) ^ w) μ := fun w =>
    (hdm.complex_ofReal.pow_const w).aestronglyMeasurable
  have hF_meas : ∀ s : ℂ,
      AEStronglyMeasurable (fun x => c x * (d x : ℂ) ^ (s - (κ : ℂ))) μ :=
    fun s => hc.mul (hpow_meas _)
  have hlog_meas : AEStronglyMeasurable (fun x => Complex.log (d x : ℂ)) μ :=
    hdm.complex_ofReal.clog.aestronglyMeasurable
  have hnorm : ∀ (s : ℂ) (x : X),
      ‖c x * (d x : ℂ) ^ (s - (κ : ℂ))‖ = ‖c x‖ * d x ^ (s.re - κ) := by
    intro s x
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hd x), Complex.sub_re,
      Complex.ofReal_re]
  have hlognorm : ∀ x, ‖Complex.log (d x : ℂ)‖ = |Real.log (d x)| := by
    intro x
    rw [← Complex.ofReal_log (hd x).le, Complex.norm_real, Real.norm_eq_abs]
  intro s₀ hs₀
  have hσ : 0 < s₀.re := hs₀
  obtain ⟨h, hh, hh2⟩ : ∃ h : ℝ, 0 < h ∧ 2 * h < s₀.re :=
    ⟨s₀.re / 4, by positivity, by linarith⟩
  have hint₀ : Integrable (fun x => c x * (d x : ℂ) ^ (s₀ - (κ : ℂ))) μ := by
    refine (hint s₀.re hσ).mono (hF_meas s₀) (Eventually.of_forall fun x => ?_)
    rw [hnorm, hnorm, Complex.ofReal_re]
  have hbound_int : Integrable (fun x => 2 / h *
      (‖c x * (d x : ℂ) ^ (((s₀.re - 2 * h : ℝ) : ℂ) - (κ : ℂ))‖ +
        ‖c x * (d x : ℂ) ^ (((s₀.re + 2 * h : ℝ) : ℂ) - (κ : ℂ))‖)) μ :=
    ((hint _ (by linarith)).norm.add (hint _ (by linarith)).norm).const_mul (2 / h)
  have hdiff : ∀ x, ∀ s ∈ ball s₀ h,
      HasDerivAt (fun s => c x * (d x : ℂ) ^ (s - (κ : ℂ)))
        (c x * ((d x : ℂ) ^ (s - (κ : ℂ)) * Complex.log (d x : ℂ))) s := by
    intro x s _
    have h1 : HasDerivAt (fun s : ℂ => s - (κ : ℂ)) 1 s := (hasDerivAt_id s).sub_const _
    have h2 := (h1.const_cpow (c := (d x : ℂ))
      (Or.inl (by exact_mod_cast (hd x).ne'))).const_mul (c x)
    simpa using h2
  have hbound : ∀ x, ∀ s ∈ ball s₀ h,
      ‖c x * ((d x : ℂ) ^ (s - (κ : ℂ)) * Complex.log (d x : ℂ))‖ ≤ 2 / h *
        (‖c x * (d x : ℂ) ^ (((s₀.re - 2 * h : ℝ) : ℂ) - (κ : ℂ))‖ +
          ‖c x * (d x : ℂ) ^ (((s₀.re + 2 * h : ℝ) : ℂ) - (κ : ℂ))‖) := by
    intro x s hs
    have hre : |s.re - s₀.re| < h := by
      rw [mem_ball, dist_eq_norm] at hs
      have := Complex.abs_re_le_norm (s - s₀)
      rw [Complex.sub_re] at this
      linarith
    have hre' := abs_lt.mp hre
    rw [hnorm, hnorm, Complex.ofReal_re, Complex.ofReal_re, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hd x), Complex.sub_re, Complex.ofReal_re,
      hlognorm]
    have key := rpow_mul_abs_log_le (r := d x) (u := s.re - κ)
      (A := s₀.re - 2 * h - κ) (B := s₀.re + 2 * h - κ) (hd x) hh
      (by linarith) (by linarith)
    have hc0 := norm_nonneg (c x)
    calc ‖c x‖ * (d x ^ (s.re - κ) * |Real.log (d x)|)
        ≤ ‖c x‖ * (2 / h * (d x ^ (s₀.re - 2 * h - κ) + d x ^ (s₀.re + 2 * h - κ))) :=
          mul_le_mul_of_nonneg_left key hc0
      _ = 2 / h * (‖c x‖ * d x ^ (s₀.re - 2 * h - κ) +
            ‖c x‖ * d x ^ (s₀.re + 2 * h - κ)) := by ring
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => c x * (d x : ℂ) ^ (s - (κ : ℂ)))
    (F' := fun s x => c x * ((d x : ℂ) ^ (s - (κ : ℂ)) * Complex.log (d x : ℂ)))
    (ball_mem_nhds s₀ hh) (Eventually.of_forall fun s => hF_meas s) hint₀
    (hc.mul ((hpow_meas _).mul hlog_meas))
    (Eventually.of_forall hbound) hbound_int (Eventually.of_forall hdiff)
  exact hderiv.2.differentiableAt.differentiableWithinAt

end Langlands.Analysis

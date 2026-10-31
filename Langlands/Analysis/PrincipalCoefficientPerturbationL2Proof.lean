import Langlands.Analysis.PrincipalCoefficientPerturbationL2Statement
import Langlands.Analysis.ConstantCoefficientEllipticL2EstimateProof
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-! # Principal coefficient absorption -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology
set_option autoImplicit false

namespace Langlands.Analysis

variable {d r : ℕ}

/-- Absorb a small principal coefficient perturbation using the published Fourier estimate. -/
theorem principalCoefficientPerturbationL2 : PrincipalCoefficientPerturbationL2Statement d r := by
  have hfourier := (constantCoefficientEllipticL2Estimate (d := d) (r := r))
  classical
  intro a₀ c hc hell a F hsmooth hcompact hsmall
  let e := EuclideanSpace.basisFun (Fin d) ℝ
  let t (w : Fin r → Fin d) (x : EuclideanSpace ℝ (Fin d)) :=
    iteratedFDeriv ℝ r F x (fun j => e (w j))
  let T (x : EuclideanSpace ℝ (Fin d)) :
      EuclideanSpace ℂ (Fin r → Fin d) := WithLp.toLp 2 (fun w => t w x)
  let P₀ (x : EuclideanSpace ℝ (Fin d)) := ∑ w, a₀ w * t w x
  let P (x : EuclideanSpace ℝ (Fin d)) := ∑ w, a w x * t w x
  have htcont (w : Fin r → Fin d) : Continuous (t w) := by
    exact (hsmooth.continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).eval_const (fun j : Fin r => e (w j))
  have hTcont : Continuous T :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi htcont)
  have hTcompact : HasCompactSupport T := by
    apply (hcompact.iteratedFDeriv (𝕜 := ℝ) r).mono
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    apply PiLp.ext
    intro w
    simp [T, t, hx]
  have hTfinite : eLpNorm T 2 volume ≠ ⊤ :=
    (hTcont.memLp_of_hasCompactSupport hTcompact).eLpNorm_ne_top
  have hP₀cont : Continuous P₀ := by
    exact continuous_finsetSum _ (fun w _ => continuous_const.mul (htcont w))
  have hTnorm (x : EuclideanSpace ℝ (Fin d)) :
      ‖T x‖ = Real.sqrt (∑ w : Fin r → Fin d, ‖t w x‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
  have hfour := hfourier a₀ c hc hell F hsmooth hcompact
  change eLpNorm (fun x => Real.sqrt (∑ w : Fin r → Fin d, ‖t w x‖ ^ 2)) 2 volume ≤
    ENNReal.ofReal c⁻¹ * eLpNorm P₀ 2 volume at hfour
  have hleft :
      eLpNorm (fun x => Real.sqrt (∑ w : Fin r → Fin d, ‖t w x‖ ^ 2)) 2 volume =
        eLpNorm T 2 volume := by
    rw [← eLpNorm_norm T hTcont.aestronglyMeasurable]
    simp only [hTnorm]
  rw [hleft] at hfour ⊢
  change eLpNorm T 2 volume ≤ ENNReal.ofReal (2 * c⁻¹) * eLpNorm P 2 volume
  by_cases hPtop : eLpNorm P 2 volume = ⊤
  · rw [hPtop, ENNReal.mul_top (by positivity)]
    exact le_top
  have hPmeas : AEStronglyMeasurable P volume :=
    aestronglyMeasurable_of_eLpNorm_ne_top hPtop
  let Q := P₀ - P
  have hQmeas : AEStronglyMeasurable Q volume :=
    hP₀cont.aestronglyMeasurable.sub hPmeas
  have hQpoint (x : EuclideanSpace ℝ (Fin d)) : ‖Q x‖ ≤ c / 2 * ‖T x‖ := by
    have hQeq : Q x = ∑ w : Fin r → Fin d, (a₀ w - a w x) * t w x := by
      simp only [Q, Pi.sub_apply, P₀, P, ← Finset.sum_sub_distrib, sub_mul]
    by_cases hx : x ∈ tsupport F
    · calc
        ‖Q x‖ ≤ ∑ w : Fin r → Fin d, ‖a₀ w - a w x‖ * ‖t w x‖ := by
          rw [hQeq]
          simpa only [norm_mul] using norm_sum_le
            (s := Finset.univ) (f := fun w => (a₀ w - a w x) * t w x)
        _ ≤ ∑ w : Fin r → Fin d, ‖a₀ w - a w x‖ * ‖T x‖ := by
          apply Finset.sum_le_sum
          intro w _
          exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (T x) w) (norm_nonneg _)
        _ = (∑ w : Fin r → Fin d, ‖a₀ w - a w x‖) * ‖T x‖ :=
          (Finset.sum_mul ..).symm
        _ ≤ c / 2 * ‖T x‖ :=
          mul_le_mul_of_nonneg_right (hsmall x hx) (norm_nonneg _)
    · have hzero : iteratedFDeriv ℝ r F x = 0 := by
        by_contra hne
        exact hx (support_iteratedFDeriv_subset r hne)
      have htzero : ∀ w : Fin r → Fin d, t w x = 0 := by
        intro w
        simp [t, hzero]
      rw [hQeq]
      simp only [htzero, mul_zero, Finset.sum_const_zero, norm_zero]
      positivity
  have hQbound := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hQmeas
    (Filter.Eventually.of_forall hQpoint) 2
  have hP₀bound : eLpNorm P₀ 2 volume ≤
      eLpNorm P 2 volume + ENNReal.ofReal (c / 2) * eLpNorm T 2 volume := by
    have hdecomp : P₀ = P + Q := by
      dsimp [Q]
      abel
    calc
      eLpNorm P₀ 2 volume ≤ eLpNorm P 2 volume + eLpNorm Q 2 volume := by
        rw [hdecomp]
        exact eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add le_rfl hQbound
  have habs : eLpNorm T 2 volume ≤
      ENNReal.ofReal c⁻¹ *
        (eLpNorm P 2 volume + ENNReal.ofReal (c / 2) * eLpNorm T 2 volume) :=
    hfour.trans (mul_le_mul' le_rfl hP₀bound)
  have hrhsfinite : ENNReal.ofReal c⁻¹ *
      (eLpNorm P 2 volume + ENNReal.ofReal (c / 2) * eLpNorm T 2 volume) ≠ ⊤ := by
    finiteness
  have habsreal := (ENNReal.toReal_le_toReal hTfinite hrhsfinite).mpr habs
  simp only [ENNReal.toReal_mul, ENNReal.toReal_add hPtop
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTfinite),
    ENNReal.toReal_ofReal (inv_nonneg.mpr hc.le),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ c / 2)] at habsreal
  have hreal : (eLpNorm T 2 volume).toReal ≤
      (2 * c⁻¹) * (eLpNorm P 2 volume).toReal := by
    have hcancel : c⁻¹ * (c / 2) = 1 / 2 := by
      field_simp
    have hexpand :
        c⁻¹ * ((eLpNorm P 2 volume).toReal +
          c / 2 * (eLpNorm T 2 volume).toReal) =
        c⁻¹ * (eLpNorm P 2 volume).toReal +
          (1 / 2) * (eLpNorm T 2 volume).toReal := by
      rw [mul_add, ← mul_assoc, hcancel]
    rw [hexpand] at habsreal
    linarith
  apply (ENNReal.toReal_le_toReal hTfinite
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPtop)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * c⁻¹)]
    using hreal

end Langlands.Analysis

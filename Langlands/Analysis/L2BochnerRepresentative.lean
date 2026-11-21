import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.Prod

/-! # Pointwise representatives of Bochner integrals in `L²` -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Langlands.Analysis

/-- If the fibres of a jointly measurable scalar function represent a Bochner-integrable
family in `L²`, the pointwise integral represents its Bochner integral. -/
theorem coeFn_integral_l2_ae_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SFinite ν]
    {A : Y → Lp ℂ 2 μ} {f : Y × X → ℂ} (hA : Integrable A ν)
    (hf : AEStronglyMeasurable f (ν.prod μ))
    (hrep : ∀ᵐ y ∂ν, (A y : X → ℂ) =ᵐ[μ] fun x => f (y, x)) :
    ((∫ y, A y ∂ν : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => ∫ y, f (y, x) ∂ν := by
  classical
  have htest (s : Set X) (hs : MeasurableSet s) (hμs : μ s < ∞) :
      IntegrableOn (fun x => (∫ y, A y ∂ν : Lp ℂ 2 μ) x) s μ ∧
      IntegrableOn (fun x => ∫ y, f (y, x) ∂ν) s μ ∧
      (∫ x in s, (∫ y, A y ∂ν : Lp ℂ 2 μ) x ∂μ) =
        ∫ x in s, (∫ y, f (y, x) ∂ν) ∂μ := by
    let χ : Lp ℂ 2 μ := indicatorConstLp 2 hs hμs.ne 1
    let B := ContinuousLinearMap.mul ℂ ℂ
    let L : Lp ℂ 2 μ →L[ℂ] Lp ℂ 1 μ := (B.holderL μ 2 2 1).flip χ
    have hL (a : Lp ℂ 2 μ) : (L a : X → ℂ) =ᵐ[μ] s.indicator a := by
      have hχ : (χ : X → ℂ) =ᵐ[μ] s.indicator (fun _ => (1 : ℂ)) := indicatorConstLp_coeFn
      filter_upwards [B.coeFn_holder (r := 1) a χ, hχ] with x hx hχx
      change B.holder 1 a χ x = _
      rw [hx]
      change a x * χ x = _
      rw [hχx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    have hLi (a : Lp ℂ 2 μ) : IntegrableOn (a : X → ℂ) s μ :=
      (integrable_indicator_iff hs).1 ((L1.integrable_coeFn (L a)).congr (hL a))
    have hLn (a : Lp ℂ 2 μ) : ‖L a‖ = ∫ x in s, ‖a x‖ ∂μ := by
      rw [L1.norm_eq_integral_norm, ← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [hL a] with x hx
      rw [hx]
      exact norm_indicator_eq_indicator_norm _ _
    let J : Lp ℂ 2 μ →L[ℂ] ℂ := (L1.integralCLM' ℂ).comp L
    have hJ (a : Lp ℂ 2 μ) : J a = ∫ x in s, a x ∂μ := by
      change L1.integralCLM' ℂ (L a) = _
      rw [← L1.integral_eq', L1.integral_eq_integral, ← integral_indicator hs]
      exact integral_congr_ae (hL a)
    let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
    have hf' : AEStronglyMeasurable f (ν.prod (μ.restrict s)) :=
      hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hfr : Integrable f (ν.prod (μ.restrict s)) := by
      apply (integrable_prod_iff hf').2
      refine ⟨?_, ?_⟩
      · filter_upwards [hrep] with y hy
        exact (hLi (A y)).congr (ae_restrict_of_ae hy)
      · refine (L.integrable_comp hA).norm.congr ?_
        filter_upwards [hrep] with y hy
        exact (hLn (A y)).trans (integral_congr_ae (ae_restrict_of_ae (hy.fun_comp norm)))
    refine ⟨hLi _, hfr.integral_prod_right, ?_⟩
    calc
      _ = J (∫ y, A y ∂ν) := (hJ _).symm
      _ = ∫ y, J (A y) ∂ν := (J.integral_comp_comm hA).symm
      _ = ∫ y, (∫ x in s, f (y, x) ∂μ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hrep] with y hy
        exact (hJ (A y)).trans (integral_congr_ae (ae_restrict_of_ae hy))
      _ = _ := integral_integral_swap hfr
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s hs hμs => (htest s hs hμs).1)
    (fun s hs hμs => (htest s hs hμs).2.1)
    (fun s hs hμs => (htest s hs hμs).2.2)

end Langlands.Analysis

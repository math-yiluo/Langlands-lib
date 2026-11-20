import Langlands.Analysis.CompactParameterSmoothness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! # Smooth integration in a real interval with parameters -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

set_option autoImplicit false

namespace Langlands.Analysis

variable {X E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integration over a compact space with a finite measure is a continuous
linear map on the space of continuous vector-valued functions. -/
def compactContinuousIntegralCLM (μ : Measure X) [IsFiniteMeasure μ] : C(X, F) →L[ℝ] F := by
  let L : C(X, F) →ₗ[ℝ] F :=
    { toFun := fun f => ∫ x, f x ∂μ
      map_add' := by
        intro f g
        exact integral_add
          (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
  refine L.mkContinuous (μ.real univ) (fun f => ?_)
  change ‖∫ x, f x ∂μ‖ ≤ _
  rw [mul_comm]
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall f.norm_coe_le_norm)

@[simp]
theorem compactContinuousIntegralCLM_apply (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, F)) :
    compactContinuousIntegralCLM μ f = ∫ x, f x ∂μ := rfl

/-- Integrating a smooth family over a fixed compact interval gives a smooth
function of the parameters. -/
theorem contDiff_intervalIntegral_of_joint {h : E × ℝ → F} (hh : ContDiff ℝ ∞ h)
    {a b : ℝ} (hab : a ≤ b) : ContDiff ℝ ∞ (fun x => ∫ t in a..b, h (x, t)) := by
  let S := Icc a b
  have : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_Icc
  let μ : Measure S := volume.comap Subtype.val
  have hS : MeasurableSet S := measurableSet_Icc
  have : IsFiniteMeasure μ := ⟨by
    change volume.comap (Subtype.val : S → ℝ) univ < ⊤
    rw [Measure.comap_apply _ Subtype.val_injective
      (fun s hs => (MeasurableEmbedding.subtype_coe hS).measurableSet_image' hs) _ MeasurableSet.univ,
      image_univ, Subtype.range_coe]
    exact isCompact_Icc.measure_lt_top⟩
  let j : C(S, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  let H (x : E) : C(S, F) :=
    ⟨fun t => h (x, t.val), hh.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hH : ContDiff ℝ ∞ H := by
    apply contDiffOn_univ.mp
    exact contDiffOn_infty_compactFamily_of_joint (f := H) j isOpen_univ isOpen_univ
      (fun _ => mem_univ _) hh.contDiffOn (fun _ _ _ => rfl)
  have heq : (fun x => ∫ t in a..b, h (x, t)) = fun x => compactContinuousIntegralCLM μ (H x) := by
    funext x
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      compactContinuousIntegralCLM_apply]
    exact (integral_subtype_comap hS (fun t => h (x, t))).symm
  rw [heq]
  exact (compactContinuousIntegralCLM μ).contDiff.comp hH

/-- An interval integral with a smooth integrand has a jointly smooth indefinite
integral in the upper endpoint and the other parameters. -/
theorem contDiff_intervalIntegral_to_variable {h : ℝ × E → F} (hh : ContDiff ℝ ∞ h) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => ∫ t in a..p.1, h (t, p.2)) := by
  let g : (ℝ × E) × ℝ → F := fun q => h ((q.1.1 - a) * q.2 + a, q.1.2)
  have hg : ContDiff ℝ ∞ g := hh.comp (by fun_prop)
  have hI := contDiff_intervalIntegral_of_joint hg (show (0 : ℝ) ≤ 1 from zero_le_one)
  have heq : (fun p : ℝ × E => ∫ t in a..p.1, h (t, p.2)) =
      fun p => (p.1 - a) • ∫ t in (0 : ℝ)..1, g (p, t) := by
    funext p
    change _ = (p.1 - a) • ∫ t in (0 : ℝ)..1, (fun u => h (u, p.2)) ((p.1 - a) * t + a)
    simpa only [mul_zero, zero_add, mul_one, sub_add_cancel] using
      (intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1)
        (fun u => h (u, p.2)) (p.1 - a) a).symm
  rw [heq]
  exact (contDiff_fst.sub contDiff_const).smul hI

end Langlands.Analysis

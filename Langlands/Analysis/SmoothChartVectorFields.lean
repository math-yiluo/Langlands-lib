import Langlands.HarmonicAnalysis.Distribution.SmoothChartVectorField
import Langlands.Analysis.SmoothChartTestPullback

/-! # Vector fields and test function differentiation in a smooth chart -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function TopologicalSpace
open scoped ContDiff Distributions Topology

namespace Langlands.Analysis

universe u v s

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coordinate field has velocity `v` wherever the forward
differential sends `v` to the original field. -/
theorem chartVectorField_eq_of_fderiv (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    (V : F → F) {x : E} (hx : x ∈ e.source) (w : E) (hw : fderiv ℝ e x w = V (e x)) :
    Langlands.HarmonicAnalysis.chartVectorField e V x = w := by
  have h : ((e.symm : F → E) ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy using e.left_inv hy
  have hd := h.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x ((hs.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt
    (by simp)) ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)),
    fderiv_id] at hd
  have hv := DFunLike.congr_fun hd w
  change fderiv ℝ e.symm (e x) (fderiv ℝ e x w) = w at hv
  rwa [hw] at hv

variable {𝕜 : Type s} [RCLike 𝕜]

/-- Differentiating a transported test along a field agrees with
transporting its derivative in chart coordinates. Equality of the
coordinate field on the original test's support suffices. -/
theorem smoothChartTestPullback_vectorField (e : OpenPartialHomeomorph E F)
    (hs : ContDiffOn ℝ ∞ e.symm e.target) (V : F → F) (W : E → E)
    (f g : 𝓓(⟨e.source, e.open_source⟩, 𝕜))
    (hg : ∀ x, g x = fderiv ℝ f x (W x))
    (hW : ∀ x ∈ tsupport f, W x = Langlands.HarmonicAnalysis.chartVectorField e V x) (y : F) :
    smoothChartTestPullback e.symm hs g y =
      fderiv ℝ (smoothChartTestPullback e.symm hs f : F → 𝕜) y (V y) := by
  by_cases hy : y ∈ e.target
  · rw [smoothChartTestPullback_apply e.symm hs g hy, hg, fderiv_smoothChartTestPullback e.symm hs f hy,
      ContinuousLinearMap.comp_apply]
    by_cases hx : e.symm y ∈ tsupport f
    · rw [hW _ hx, Langlands.HarmonicAnalysis.chartVectorField, e.right_inv hy]
    · have hzero : fderiv ℝ f (e.symm y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
      simp [hzero]
  · rw [smoothChartTestPullback_apply_of_notMem e.symm hs g hy]
    have hzero : fderiv ℝ (smoothChartTestPullback e.symm hs f : F → 𝕜) y = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hy ((smoothChartTestPullback e.symm hs f).tsupport_subset
          (tsupport_fderiv_subset ℝ h)))
    exact (DFunLike.congr_fun hzero (V y)).symm

end Langlands.Analysis

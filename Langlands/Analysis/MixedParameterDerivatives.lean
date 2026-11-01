import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Commutation of parameter and evaluation derivatives -/

noncomputable section
universe u v w
open scoped Topology ContDiff
open Filter Set
set_option autoImplicit false

namespace Langlands.Analysis

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem fderiv_fst_slice_apply {h : E × F → G} {x : E} {y : F}
    (hh : DifferentiableAt ℝ h (x, y)) (d : E) :
    fderiv ℝ (fun z => h (z, y)) x d = fderiv ℝ h (x, y) (d, 0) := by
  have hi : HasFDerivAt (fun z : E => (z, y))
      (ContinuousLinearMap.inl ℝ E F) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const (𝕜 := ℝ) y x)
  have hs := hh.hasFDerivAt.comp x hi
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply] using congrArg (fun L => L d) hs.fderiv

theorem fderiv_snd_slice_apply {h : E × F → G} {x : E} {y : F}
    (hh : DifferentiableAt ℝ h (x, y)) (d : F) :
    fderiv ℝ (fun z => h (x, z)) y d = fderiv ℝ h (x, y) (0, d) := by
  have hi : HasFDerivAt (fun z : F => (x, z))
      (ContinuousLinearMap.inr ℝ E F) y :=
    (hasFDerivAt_const (𝕜 := ℝ) x y).prodMk (hasFDerivAt_id y)
  have hs := hh.hasFDerivAt.comp y hi
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply] using congrArg (fun L => L d) hs.fderiv

/-- The two partial derivatives commute on an open product domain. Directions
belong to separate factors and are held constant during the outer derivative. -/
theorem fderiv_fst_snd_comm
    {h : E × F → G} {s : Set E} {t : Set F}
    (hs : IsOpen s) (ht : IsOpen t)
    (hh : ContDiffOn ℝ ∞ h (s ×ˢ t))
    {x : E} (hx : x ∈ s) {y : F} (hy : y ∈ t) (d : E) (e : F) :
    fderiv ℝ (fun z => fderiv ℝ (fun q => h (z, q)) y e) x d =
      fderiv ℝ (fun q => fderiv ℝ (fun z => h (z, q)) x d) y e := by
  have hAt (z : E) (hz : z ∈ s) (q : F) (hq : q ∈ t) :
      ContDiffAt ℝ ∞ h (z, q) :=
    hh.contDiffAt ((hs.prod ht).mem_nhds ⟨hz, hq⟩)
  have hD : DifferentiableAt ℝ (fderiv ℝ h) (x, y) :=
    ((hAt x hx y hy).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have heqL :
      (fun z => fderiv ℝ (fun q => h (z, q)) y e) =ᶠ[𝓝 x]
        (fun z => fderiv ℝ h (z, y) (0, e)) := by
    filter_upwards [hs.mem_nhds hx] with z hz
    exact fderiv_snd_slice_apply ((hAt z hz y hy).differentiableAt (by simp)) e
  have heqR :
      (fun q => fderiv ℝ (fun z => h (z, q)) x d) =ᶠ[𝓝 y]
        (fun q => fderiv ℝ h (x, q) (d, 0)) := by
    filter_upwards [ht.mem_nhds hy] with q hq
    exact fderiv_fst_slice_apply ((hAt x hx q hq).differentiableAt (by simp)) d
  rw [heqL.fderiv_eq, heqR.fderiv_eq]
  have hiL : HasFDerivAt (fun z : E => (z, y))
      (ContinuousLinearMap.inl ℝ E F) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const (𝕜 := ℝ) y x)
  have hiR : HasFDerivAt (fun z : F => (x, z))
      (ContinuousLinearMap.inr ℝ E F) y :=
    (hasFDerivAt_const (𝕜 := ℝ) x y).prodMk (hasFDerivAt_id y)
  have hL := (hD.hasFDerivAt.comp x hiL).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) ((0 : E), e) x)
  have hR := (hD.hasFDerivAt.comp y hiR).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (d, (0 : F)) y)
  calc
    _ = fderiv ℝ (fderiv ℝ h) (x, y) (d, 0) (0, e) := by
      simpa using congrArg (fun L => L d) hL.fderiv
    _ = fderiv ℝ (fderiv ℝ h) (x, y) (0, e) (d, 0) :=
      (hAt x hx y hy).isSymmSndFDerivAt (by simp) (d, 0) (0, e)
    _ = _ := by
      simpa using (congrArg (fun L => L e) hR.fderiv).symm

end Langlands.Analysis

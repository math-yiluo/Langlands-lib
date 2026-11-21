import Langlands.Analysis.SmoothChartTestPullback
import Mathlib.Analysis.Distribution.Support

/-! # Distribution transport to an open smooth chart -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped ContDiff Distributions

namespace Langlands.Analysis

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens F}

/-- Transport a chart test to the target and regard it as an ambient test. -/
def smoothChartAmbientTest (e : OpenPartialHomeomorph E F)
    (hs : ContDiffOn ℝ ∞ e.symm e.target) :
    𝓓(⟨e.source, e.open_source⟩, ℂ) →L[ℂ] 𝓓(Ω, ℂ) :=
  (TestFunction.monoCLM ℂ).comp (smoothChartTestPullback e.symm hs)

theorem coe_smoothChartAmbientTest (e : OpenPartialHomeomorph E F)
    (hs : ContDiffOn ℝ ∞ e.symm e.target) (heΩ : e.target ⊆ Ω)
    (f : 𝓓(⟨e.source, e.open_source⟩, ℂ)) :
    ((smoothChartAmbientTest (Ω := Ω) e hs f : 𝓓(Ω, ℂ)) : F → ℂ) =
      smoothChartTestPullback e.symm hs f := by
  have he : (⟨e.target, e.open_target⟩ : Opens F) ≤ Ω := heΩ
  simp [smoothChartAmbientTest, he]

/-- The ambient distribution may be tested in chart coordinates. -/
theorem isVanishingOn_smoothChartAmbientTest (e : OpenPartialHomeomorph E F)
    (hs : ContDiffOn ℝ ∞ e.symm e.target) (heΩ : e.target ⊆ Ω)
    (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) {U : Set E} {V : Set F} (hUV : MapsTo e (e.source ∩ U) V)
    (hT : Distribution.IsVanishingOn T V) :
    Distribution.IsVanishingOn (T.comp (smoothChartAmbientTest e hs)) U := by
  intro f hf
  apply hT
  change tsupport (smoothChartAmbientTest (Ω := Ω) e hs f : F → ℂ) ⊆ V
  rw [coe_smoothChartAmbientTest (Ω := Ω) e hs heΩ f]
  apply (tsupport_smoothChartTestPullback_subset e.symm hs f).trans
  rintro _ ⟨x, hx, rfl⟩
  exact hUV ⟨f.tsupport_subset hx, hf hx⟩

/-- Vanishing of the chart distribution transfers back to the chart image. -/
theorem isVanishingOn_image_of_smoothChartAmbientTest (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    (heΩ : e.target ⊆ Ω) (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) {U : Set E} (hU : U ⊆ e.source)
    (hT : Distribution.IsVanishingOn (T.comp (smoothChartAmbientTest e hs)) U) :
    Distribution.IsVanishingOn T (e '' U) := by
  intro f hf
  have hg₀ : (e '' U : Set F) ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hU hx)
  let g : 𝓓(⟨e.target, e.open_target⟩, ℂ) :=
    ⟨f, f.contDiff, f.hasCompactSupport, hf.trans hg₀⟩
  let g' := smoothChartTestPullback e he g
  have hg' : tsupport g' ⊆ U := by
    apply (tsupport_smoothChartTestPullback_subset e he g).trans
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hf hy
    rwa [e.left_inv (hU hx)]
  have h := hT g' hg'
  have hfg : smoothChartAmbientTest e hs g' = f := by
    apply TestFunction.ext
    intro y
    have hx := congrFun (coe_smoothChartAmbientTest e hs heΩ g') y
    rw [smoothChartTestPullback_symm_apply e he hs g] at hx
    exact hx
  change T (smoothChartAmbientTest e hs g') = 0 at h
  rwa [hfg] at h

end Langlands.Analysis

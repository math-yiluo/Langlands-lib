import Langlands.HarmonicAnalysis.Distribution.SmoothTestCharts
import Mathlib.Analysis.Distribution.Support

/-! # Transport between full-space tests and tests in smooth coordinates -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {X E E' F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pull back a test defined on an entire real normed space by a continuous
linear equivalence. -/
def fullSmoothTestPullbackCLM (A : E ≃L[ℝ] X) :
    𝓓((⊤ : Opens X), ℝ) →L[ℝ] 𝓓((⊤ : Opens E), ℝ) :=
  pullbackChartTestCLM A.toHomeomorph.toOpenPartialHomeomorph
    A.toContinuousLinearMap.contDiff.contDiffOn

@[simp]
theorem fullSmoothTestPullbackCLM_apply (A : E ≃L[ℝ] X)
    (φ : 𝓓((⊤ : Opens X), ℝ)) (x : E) :
    fullSmoothTestPullbackCLM A φ x = φ (A x) :=
  pullbackChartTestCLM_apply_of_mem A.toHomeomorph.toOpenPartialHomeomorph
    A.toContinuousLinearMap.contDiff.contDiffOn φ (mem_univ x)

variable (e : OpenPartialHomeomorph E X) (he : ContDiffOn ℝ ∞ e.symm e.target)

/-- Push a coordinate test through the inverse chart and extend it by zero to
the whole ambient space. -/
def chartTestToFullCLM : 𝓓(chartSource e, ℝ) →L[ℝ] 𝓓((⊤ : Opens X), ℝ) :=
  (TestFunction.monoCLM ℝ).comp (pullbackChartTestCLM e.symm he)

private theorem coe_chartTestToFullCLM (φ : 𝓓(chartSource e, ℝ)) :
    (chartTestToFullCLM e he φ : X → ℝ) = ⇑(pullbackChartTestCLM e.symm he φ) := by
  change ((TestFunction.monoCLM ℝ (pullbackChartTestCLM e.symm he φ) :
    𝓓((⊤ : Opens X), ℝ)) : X → ℝ) = _
  simp

theorem chartTestToFullCLM_apply_of_mem (φ : 𝓓(chartSource e, ℝ))
    {p : X} (hp : p ∈ e.target) :
    chartTestToFullCLM e he φ p = φ (e.symm p) :=
  (congrFun (coe_chartTestToFullCLM e he φ) p).trans
    (pullbackChartTestCLM_apply_of_mem e.symm he φ hp)

theorem chartTestToFullCLM_apply_of_notMem (φ : 𝓓(chartSource e, ℝ))
    {p : X} (hp : p ∉ e.target) :
    chartTestToFullCLM e he φ p = 0 :=
  (congrFun (coe_chartTestToFullCLM e he φ) p).trans
    ((pullbackChartTestCLM e.symm he φ).zero_on_compl hp)

theorem tsupport_chartTestToFullCLM_subset (φ : 𝓓(chartSource e, ℝ)) :
    tsupport (chartTestToFullCLM e he φ) ⊆ e '' tsupport φ := by
  rw [coe_chartTestToFullCLM]
  exact tsupport_pullbackChartTestCLM_subset e.symm he φ

/-- Express a full-space distribution in a chart by applying it to tests
transported through the inverse chart. -/
def chartFullDistribution (D : 𝓓'((⊤ : Opens X), F)) : 𝓓'(chartSource e, F) :=
  D.comp (chartTestToFullCLM e he)

@[simp]
theorem chartFullDistribution_apply (D : 𝓓'((⊤ : Opens X), F)) (φ : 𝓓(chartSource e, ℝ)) :
    chartFullDistribution e he D φ = D (chartTestToFullCLM e he φ) := rfl

theorem isVanishingOn_chartFullDistribution (D : 𝓓'((⊤ : Opens X), F)) {s : Set X} {t : Set E}
    (hD : Distribution.IsVanishingOn D s) (hst : e '' (t ∩ e.source) ⊆ s) :
    Distribution.IsVanishingOn (chartFullDistribution e he D) t := by
  intro φ hφ
  apply hD
  refine (tsupport_chartTestToFullCLM_subset e he φ).trans
    ((image_mono ?_).trans hst)
  exact subset_inter hφ φ.tsupport_subset

/-- Transfer an ambient covariance law to two coordinate tests. The pullback
ambient support must be contained in the first chart's target. -/
theorem chartFullDistribution_eval_of_covariance
    (e' : OpenPartialHomeomorph E' X) (he' : ContDiffOn ℝ ∞ e'.symm e'.target)
    (D : 𝓓'((⊤ : Opens X), F)) (A : X ≃L[ℝ] X) (c : ℝ)
    (hD : ∀ f : 𝓓((⊤ : Opens X), ℝ), D (fullSmoothTestPullbackCLM A f) = c • D f)
    (ψ : 𝓓(chartSource e, ℝ)) (φ : 𝓓(chartSource e', ℝ))
    (hs : A ⁻¹' tsupport (chartTestToFullCLM e' he' φ) ⊆ e.target)
    (hψ : ∀ x ∈ e.source, ψ x = chartTestToFullCLM e' he' φ (A (e x))) :
    chartFullDistribution e he D ψ = c • chartFullDistribution e' he' D φ := by
  have heq : chartTestToFullCLM e he ψ =
      fullSmoothTestPullbackCLM A (chartTestToFullCLM e' he' φ) := by
    ext p
    rw [fullSmoothTestPullbackCLM_apply]
    by_cases hp : p ∈ e.target
    · rw [chartTestToFullCLM_apply_of_mem e he ψ hp]
      simpa only [e.right_inv hp] using hψ (e.symm p) (e.map_target hp)
    · rw [chartTestToFullCLM_apply_of_notMem e he ψ hp]
      exact (image_eq_zero_of_notMem_tsupport (fun hp' => hp (hs hp'))).symm
  rw [chartFullDistribution_apply, heq, hD, chartFullDistribution_apply]

end Langlands.HarmonicAnalysis

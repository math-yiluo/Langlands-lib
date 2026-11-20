import Langlands.HarmonicAnalysis.Distribution.SmoothTestCharts

/-! # Linear changes of coordinates on open smooth test spaces -/

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {E X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U : Opens E} {V : Opens X}

private def restrictedLinearTestChart (L : E ≃L[ℝ] X) (U : Opens E) :
    OpenPartialHomeomorph E X :=
  L.toHomeomorph.toOpenPartialHomeomorph.restrOpen U U.isOpen

private theorem restrictedLinearTestChart_source (L : E ≃L[ℝ] X) (U : Opens E) :
    (restrictedLinearTestChart L U).source = U := by
  change univ ∩ (U : Set E) = U
  exact univ_inter _

private theorem restrictedLinearTestChart_target (L : E ≃L[ℝ] X)
    (h : L ⁻¹' (V : Set X) = U) : (restrictedLinearTestChart L U).target = V := by
  rw [← OpenPartialHomeomorph.image_source_eq_target, restrictedLinearTestChart_source, ← h]
  exact image_preimage_eq _ L.surjective

/-- Pull back tests under a continuous linear equivalence which identifies
the two open test domains. -/
def openLinearTestPullbackCLM (L : E ≃L[ℝ] X) (_h : L ⁻¹' (V : Set X) = U) :
    𝓓(V, ℝ) →L[ℝ] 𝓓(U, ℝ) :=
  let p := restrictedLinearTestChart L U
  let hL : ContDiffOn ℝ ∞ p p.source := L.toContinuousLinearMap.contDiff.contDiffOn
  let j : 𝓓(V, ℝ) →L[ℝ] 𝓓(chartTarget p, ℝ) := TestFunction.monoCLM ℝ
  (TestFunction.monoCLM ℝ).comp ((pullbackChartTestCLM p hL).comp j)

@[simp]
theorem openLinearTestPullbackCLM_apply (L : E ≃L[ℝ] X) (h : L ⁻¹' (V : Set X) = U)
    (f : 𝓓(V, ℝ)) (x : E) : openLinearTestPullbackCLM L h f x = f (L x) := by
  let p := restrictedLinearTestChart L U
  let hL : ContDiffOn ℝ ∞ p p.source := L.toContinuousLinearMap.contDiff.contDiffOn
  let j : 𝓓(V, ℝ) →L[ℝ] 𝓓(chartTarget p, ℝ) := TestFunction.monoCLM ℝ
  have hV : V ≤ chartTarget p := (restrictedLinearTestChart_target L h).ge
  have hU : chartSource p ≤ U := (restrictedLinearTestChart_source L U).le
  have hj : (j f : X → ℝ) = f := by simp [j, hV]
  change (TestFunction.monoCLM ℝ (pullbackChartTestCLM p hL (j f)) : 𝓓(U, ℝ)) x = _
  have hcoe : ((TestFunction.monoCLM ℝ (pullbackChartTestCLM p hL (j f)) : 𝓓(U, ℝ)) : E → ℝ)
      = ⇑(pullbackChartTestCLM p hL (j f)) := by simp [hU]
  rw [show (TestFunction.monoCLM ℝ (pullbackChartTestCLM p hL (j f)) : 𝓓(U, ℝ)) x =
    pullbackChartTestCLM p hL (j f) x from congrFun hcoe x]
  by_cases hx : x ∈ p.source
  · exact (pullbackChartTestCLM_apply_of_mem p hL (j f) hx).trans (congrFun hj (L x))
  · have hx' : L x ∉ V := fun hx' => hx (by
      rwa [show p.source = (U : Set E) from restrictedLinearTestChart_source L U, ← h])
    exact ((pullbackChartTestCLM p hL (j f)).zero_on_compl hx).trans (f.zero_on_compl hx').symm

theorem lineDerivCLM_smoothTest_apply (u : E) (f : 𝓓(U, ℝ)) (x : E) :
    (TestFunction.lineDerivCLM ℝ u f : 𝓓(U, ℝ)) x = fderiv ℝ f x u := by
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  rw [(f.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]

/-- A constant derivative commutes with a linear coordinate change after
transporting its direction by the same linear map. -/
theorem openLinearTestPullbackCLM_lineDerivCLM (L : E ≃L[ℝ] X)
    (h : L ⁻¹' (V : Set X) = U) (f : 𝓓(V, ℝ)) (u : E) :
    openLinearTestPullbackCLM L h (TestFunction.lineDerivCLM ℝ (L u) f) =
      TestFunction.lineDerivCLM ℝ u (openLinearTestPullbackCLM L h f) := by
  ext x
  rw [openLinearTestPullbackCLM_apply, lineDerivCLM_smoothTest_apply, lineDerivCLM_smoothTest_apply]
  have hf : (openLinearTestPullbackCLM L h f : E → ℝ) = f ∘ L :=
    funext (openLinearTestPullbackCLM_apply L h f)
  rw [hf, ((f.contDiff.differentiable (by simp) (L x)).hasFDerivAt.comp x
    L.toContinuousLinearMap.hasFDerivAt).fderiv]
  rfl

end Langlands.HarmonicAnalysis

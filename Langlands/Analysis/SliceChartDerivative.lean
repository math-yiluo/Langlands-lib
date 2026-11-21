import Langlands.Analysis.ComplexDistributionRealTests
import Langlands.Analysis.LocalSmoothCutoff
import Langlands.Analysis.SliceJetOperators
import Langlands.Analysis.SmoothChartVectorFields

/-! # Fixed-support real test derivatives in chart coordinates -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function Set TopologicalSpace
open scoped ContDiff Distributions

namespace Langlands.Analysis

universe uX uY uM

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {M : Type uM} [NormedAddCommGroup M] [NormedSpace ℝ M]

private def compactTestFieldDeriv {K : Compacts (X × Y)} (W : X × Y → X × Y)
    (hW : ContDiff ℝ ∞ W) : 𝓓_{K}(X × Y, ℝ) →L[ℝ] 𝓓_{K}(X × Y, ℝ) :=
  (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.id ℝ (X × Y →L[ℝ] ℝ)) hW).comp
    (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤)

private theorem compactTestFieldDeriv_apply {K : Compacts (X × Y)} (W : X × Y → X × Y)
    (hW : ContDiff ℝ ∞ W) (f : 𝓓_{K}(X × Y, ℝ)) (x : X × Y) :
    compactTestFieldDeriv W hW f x = fderiv ℝ f x (W x) := by
  change (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f x) (W x) = _
  rw [ContDiffMapSupportedIn.fderivCLM_apply_of_le ℝ f (by simp)]

/-- The real fixed-support test, complexified and transported to the target. -/
def transportCompactRealTest (e : OpenPartialHomeomorph (X × Y) M)
    (hs : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Compacts (X × Y)} (hK : (K : Set (X × Y)) ⊆ e.source) (f : 𝓓_{K}(X × Y, ℝ)) :
    𝓓(⟨e.target, e.open_target⟩, ℂ) :=
  smoothChartTestPullback e.symm hs (TestFunction.postcompCLM Complex.ofRealCLM
    (TestFunction.ofSupportedIn hK f))

/-- A fixed-support derivative along the transformed field commutes
with transport and complexification of the real tests. -/
theorem transportCompactRealTest_derivative (e : OpenPartialHomeomorph (X × Y) M)
    (hs : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Compacts (X × Y)} (hK : (K : Set (X × Y)) ⊆ e.source)
    (V : M → M) (W : X × Y → X × Y)
    (hW : EqOn W (Langlands.HarmonicAnalysis.chartVectorField e V) K)
    (f g : 𝓓_{K}(X × Y, ℝ)) (hg : ∀ x, g x = fderiv ℝ f x (W x)) (y : M) :
    transportCompactRealTest e hs hK g y =
      fderiv ℝ (transportCompactRealTest e hs hK f : M → ℂ) y (V y) := by
  let f₀ : 𝓓(⟨e.source, e.open_source⟩, ℂ) :=
    TestFunction.postcompCLM Complex.ofRealCLM (TestFunction.ofSupportedIn hK f)
  let g₀ : 𝓓(⟨e.source, e.open_source⟩, ℂ) :=
    TestFunction.postcompCLM Complex.ofRealCLM (TestFunction.ofSupportedIn hK g)
  have hsupp : tsupport f₀ ⊆ (K : Set (X × Y)) :=
    (tsupport_comp_subset Complex.ofRealCLM.map_zero (f : X × Y → ℝ)).trans f.tsupport_subset
  have hder (x : X × Y) : g₀ x = fderiv ℝ f₀ x (W x) := by
    change Complex.ofRealCLM (g x) = fderiv ℝ (Complex.ofRealCLM ∘ (f : X × Y → ℝ)) x (W x)
    rw [fderiv_comp x Complex.ofRealCLM.differentiableAt (f.contDiff.differentiable (by simp) x),
      Complex.ofRealCLM.fderiv, ContinuousLinearMap.comp_apply, hg]
  exact smoothChartTestPullback_vectorField e hs V W f₀ g₀ hder (fun _ hx => hW (hsupp hx)) y

/-- A smooth field tangent on the slice induces a fixed-support real
test derivative that preserves vanishing jets and intertwines with
the actual derivative of the transported test. -/
theorem exists_tangentChartDerivative [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (e : OpenPartialHomeomorph (X × Y) M)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Compacts (X × Y)} (hK : (K : Set (X × Y)) ⊆ e.source)
    (V : M → M) (hV : ContDiffOn ℝ ∞ V e.target)
    (hWt : ∀ x : X, (x, 0) ∈ e.source → (Langlands.HarmonicAnalysis.chartVectorField e V (x, 0)).2 = 0) :
    ∃ D : 𝓓_{K}(X × Y, ℝ) →ₗ[ℝ] 𝓓_{K}(X × Y, ℝ),
      (∀ m (f : 𝓓_{K}(X × Y, ℝ)), IsFlatOnZeroSlice m (f : X × Y → ℝ) →
        IsFlatOnZeroSlice m (D f : X × Y → ℝ)) ∧
      ∀ (f : 𝓓_{K}(X × Y, ℝ)) y, transportCompactRealTest e hs hK (D f) y =
        fderiv ℝ (transportCompactRealTest e hs hK f : M → ℂ) y (V y) := by
  let F := Langlands.HarmonicAnalysis.chartVectorField e V
  obtain ⟨a, -, ha, hat, hW⟩ := exists_contDiff_cutoff_smul e.open_source K.isCompact hK
    (Langlands.HarmonicAnalysis.contDiffOn_chartVectorField (e := e) he hs hV)
  let W : X × Y → X × Y := fun x => a x • F x
  have hWF : EqOn W F K := by
    intro x hx
    change a x • F x = F x
    rw [ha hx]
    exact one_smul _ _
  have hWt' (x : X) : (W (x, 0)).2 = 0 := by
    change a (x, 0) • (F (x, 0)).2 = 0
    by_cases hx : (x, 0) ∈ e.source
    · rw [hWt x hx, smul_zero]
    · have ha₀ : a (x, 0) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hat h))
      rw [ha₀, zero_smul]
  let D := compactTestFieldDeriv (K := K) W hW
  refine ⟨D.toLinearMap, ?_, ?_⟩
  · intro m f hf
    change IsFlatOnZeroSlice m (D f : X × Y → ℝ)
    have h : (D f : X × Y → ℝ) = fun x => fderiv ℝ f x (W x) :=
      funext (compactTestFieldDeriv_apply W hW f)
    rw [h]
    exact hf.tangential f.contDiff hW hWt'
  · intro f y
    exact transportCompactRealTest_derivative e hs hK V W hWF f (D f)
      (compactTestFieldDeriv_apply W hW f) y

end Langlands.Analysis

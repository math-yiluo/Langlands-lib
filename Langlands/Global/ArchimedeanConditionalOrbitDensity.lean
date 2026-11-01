import Langlands.Analysis.ComplexSubmoduleClosure
import Langlands.Global.ArchimedeanOrbitCoefficientJointFinite
import Langlands.Global.ArchimedeanCompactComponentCoverageStatement
import Langlands.Global.ArchimedeanCompactLieOrbitDensityStatement
import Langlands.Global.ArchimedeanJointFiniteAnalyticityStatement
import Langlands.Global.ArchimedeanEnvelopingJetProof
import Langlands.Global.ArchimedeanAnalyticJetProof

/-! # Compact and enveloping orbit density from explicit analytic inputs -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The analytic and component inputs remain explicit until independently proved. -/
theorem compactLieOrbitDensity_of_analyticity_of_componentCoverage
    (han : JointFiniteAnalyticityStatement K n)
    (hcomponents : CompactComponentCoverageStatement K n) :
    CompactLieOrbitDensityStatement K n := by
  intro f hf g
  apply Langlands.Analysis.mem_topologicalClosure_of_forall_complex_annihilator
  intro ℓ hℓ
  let F := smoothOrbitCoefficient K n ℓ f
  have hfinite : IsJointFinite K n F :=
    isJointFinite_smoothOrbitCoefficient K n ℓ f hf
  have hanF := han F hfinite
  obtain ⟨k, hgk⟩ := hcomponents g
  have hzero : ∀ a : EnvelopingAlgebra K n,
      (envelopingAction K n a F).val k.val = 0 := by
    intro a
    rw [envelopingAction_smoothOrbitCoefficient_apply]
    exact hℓ _ (Submodule.subset_span ⟨(k, a), rfl⟩)
  have hjet := envelopingZeroJet K n F k.val hzero
  have hFg := analyticMatrixJetUniqueness K n F k.val hanF hjet g hgk
  change ℓ (DerivativeSmoothFunctions.rightAction K n g f) = 0
  exact hFg

end Langlands.Global.ArchimedeanGL

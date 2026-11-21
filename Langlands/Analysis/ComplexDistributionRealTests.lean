import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Support

/-! # Real tests determine a complex-linear distribution -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Distributions

namespace Langlands.Analysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

/-- A complex-linear distribution evaluated on the complexification of a real test. -/
def complexDistributionRealTests (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) : 𝓓'(Ω, ℂ) :=
  (T.restrictScalars ℝ).comp (TestFunction.postcompCLM Complex.ofRealCLM)

theorem complexDistributionRealTests_apply (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) (f : 𝓓(Ω, ℝ)) :
    complexDistributionRealTests T f = T (TestFunction.postcompCLM Complex.ofRealCLM f) :=
  rfl

/-- Vanishing can be checked on real tests with the same allowed support. -/
theorem isVanishingOn_complexDistributionRealTests_iff
    (T : 𝓓(Ω, ℂ) →L[ℂ] ℂ) (U : Set E) :
    Distribution.IsVanishingOn (complexDistributionRealTests T) U ↔
      Distribution.IsVanishingOn T U := by
  constructor
  · intro h f hf
    let re := TestFunction.postcompCLM Complex.reCLM f
    let im := TestFunction.postcompCLM Complex.imCLM f
    have hre : tsupport re ⊆ U :=
      (tsupport_comp_subset Complex.reCLM.map_zero (f : E → ℂ)).trans hf
    have him : tsupport im ⊆ U :=
      (tsupport_comp_subset Complex.imCLM.map_zero (f : E → ℂ)).trans hf
    have he : f = TestFunction.postcompCLM Complex.ofRealCLM re +
        Complex.I • TestFunction.postcompCLM Complex.ofRealCLM im := by
      ext x
      change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
      rw [mul_comm Complex.I]
      exact (Complex.re_add_im (f x)).symm
    rw [he, map_add, map_smul, ← complexDistributionRealTests_apply, ← complexDistributionRealTests_apply,
      h re hre, h im him, smul_zero, add_zero]
  · intro h f hf
    exact h _ ((tsupport_comp_subset Complex.ofRealCLM.map_zero (f : E → ℝ)).trans hf)

end Langlands.Analysis

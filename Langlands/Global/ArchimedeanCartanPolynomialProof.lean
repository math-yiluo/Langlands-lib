import Langlands.Global.ArchimedeanCartanPolynomialStatement
import Langlands.Global.ArchimedeanJointPolynomialProof

/-! # The finite joint-orbit annihilator for the actual Cartan square sum -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Specialize the actual central-plus-compact annihilator to the full square sum. -/
theorem cartanSquareSumPolynomialAnnihilation :
    CartanSquareSumPolynomialAnnihilationStatement K n := by
  intro f hf
  obtain ⟨p, hp, hd, hann⟩ := jointOrbitPolynomialAnnihilation K n f hf
    (matrixCentralCasimir K n) ((2 : ℂ) • compactCartanElement K n)
  refine ⟨p, hp, hd, ?_⟩
  have heq : centerInclusion K n (matrixCentralCasimir K n) +
      (((2 : ℂ) • compactCartanElement K n : compactEnvelopingSubalgebra K n) :
        EnvelopingAlgebra K n) = cartanSquareSum K n := by
    change centerInclusion K n (matrixCentralCasimir K n) +
      (2 : ℂ) • (compactCartanElement K n : EnvelopingAlgebra K n) = _
    exact (cartanSquareSum_eq_central_add_compact K n).symm
  intro g hg
  simpa only [heq] using hann g hg

end Langlands.Global.ArchimedeanGL

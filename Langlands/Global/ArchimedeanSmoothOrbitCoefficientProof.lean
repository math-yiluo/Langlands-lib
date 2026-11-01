import Langlands.Global.ArchimedeanSmoothOrbitCoefficientStatement
import Langlands.Global.ArchimedeanScalarOrbitDifferentiation

/-! # Smooth scalar coefficients of genuine translation orbits -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- The constructed scalar coefficient satisfies the exact scalar orbit
statement for every number field and every natural rank. -/
theorem smoothOrbitCoefficientStatement
    (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    SmoothOrbitCoefficientStatement K n := by
  intro ℓ f
  refine ⟨smoothOrbitCoefficient K n ℓ f, ?_, ?_⟩
  · exact smoothOrbitCoefficient_apply K n ℓ f
  · intro a g
    exact envelopingAction_smoothOrbitCoefficient_apply K n ℓ a f g

end Langlands.Global.ArchimedeanGL

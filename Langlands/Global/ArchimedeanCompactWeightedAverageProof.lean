import Langlands.Global.ArchimedeanCompactWeightedAverageStatement
import Langlands.Global.ArchimedeanCompactAverageOrbitClosure

/-! # Weighted compact averaging in the actual derivative topology -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Actual finite-measure compact averaging is continuous in every genuine
enveloping derivative coordinate and stays in the closed compact-orbit span. -/
theorem compactWeightedAverage : CompactWeightedAverageStatement K n := by
  intro _ _ ν _ w
  refine ⟨CompactWeightedAverage.averageCLM ν w, ?_, ?_⟩
  · exact CompactWeightedAverage.eval_averageCLM ν w
  · exact CompactWeightedAverage.average_mem_closed_compactOrbit ν w

end Langlands.Global.ArchimedeanGL

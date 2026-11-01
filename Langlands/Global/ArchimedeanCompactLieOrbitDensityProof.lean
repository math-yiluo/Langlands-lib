import Langlands.Global.ArchimedeanConditionalOrbitDensity
import Langlands.Global.ArchimedeanCompactComponentCoverageProof
import Langlands.Global.ArchimedeanJointFiniteAnalyticityProof

/-! # Density of the genuine compact and enveloping orbit -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

/-- Every group translate of a joint-finite smooth vector belongs to the
closure of its compact translates of genuine enveloping derivatives. -/
theorem compactLieOrbitDensity
    (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    CompactLieOrbitDensityStatement K n :=
  compactLieOrbitDensity_of_analyticity_of_componentCoverage K n
    (jointFiniteAnalyticity K n) (compactComponentCoverage K n)

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    CompactLieOrbitDensityStatement K n :=
  @compactLieOrbitDensity

example (K : Type u) [Field K] [NumberField K] :
    CompactLieOrbitDensityStatement K 0 :=
  compactLieOrbitDensity K 0

end Langlands.Global.ArchimedeanGL

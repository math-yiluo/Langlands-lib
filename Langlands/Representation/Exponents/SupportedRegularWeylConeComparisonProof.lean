import Langlands.Representation.Exponents.SupportedRegularWeylConeReduction
import Langlands.Representation.Classification.TemperedInductionPreservationProof

/-!
# The supported regular Weyl and cone comparison

The reduction is applied to the published preservation of analytic
temperedness by actual normalized GL induction, on each side.
-/

noncomputable section

namespace Langlands

universe uF uV1 uV2 uM1 uM2 uW1 uW2 uJ

/-- Two supported regular data with a common weak irreducible quotient have one
fine-Levi conjugacy witness giving the twisted fine equivalence, the fixed
real-parameter relation and both weighted full-diagonal cone conditions. -/
theorem glSupportedRegularWeylConeComparison :
    GLSupportedRegularWeylConeComparisonStatement.{uF, uV1, uV2, uM1, uM2, uW1, uW2, uJ} :=
  SupportedRegularWeylCone.reduction
    glTemperedInductionPreservation.{uF, uW1} glTemperedInductionPreservation.{uF, uW2}

end Langlands

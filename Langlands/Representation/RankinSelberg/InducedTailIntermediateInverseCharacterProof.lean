import Langlands.Representation.RankinSelberg.InducedTailIntermediateInverseCharacterStatement
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCharacterTransport

/-! # Inverse-character equality of actual unequal-rank zeta values -/

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW

/-- Actual unequal-rank zeta values are unchanged at the inverse additive
character, with independently supplied compatible quotient measures. -/
theorem inducedTailIntermediateInverseCharacter :
    InducedTailIntermediateInverseCharacterStatement.{uF,uV,uW} := by
  intro p _ K T n r j k hr
  exact unequalRankZetaValuesAt_scale_neg_one_compatible T n r j k hr

end Langlands.RankinSelberg

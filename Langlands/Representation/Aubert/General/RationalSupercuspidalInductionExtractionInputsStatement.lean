import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionFiniteLengthStatement
import Langlands.Representation.Aubert.General.RationalCuspidalExtractionInputs

/-! # Actual supercuspidal induction from the cuspidal extraction inputs -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- The two published inputs of actual rational cuspidal factor extraction, a
geometric filtration of every actual induced Jacquet object and proper-standard
induction exclusion, imply the finite-length part of Renard, Théorème VI.5.4,
on the actual standard families. The inputs are taken at the carrier parameter
`v` of the target's input universe. No proof is supplied here. -/
def RationalSupercuspidalInductionFiniteLengthFromExtractionInputsStatement : Prop :=
  RationalCuspidalExtractionInputsStatement.{u, v} →
    RationalSupercuspidalInductionFiniteLengthStatement.{u, v}

end Langlands.Aubert.General.RationalPointFamily

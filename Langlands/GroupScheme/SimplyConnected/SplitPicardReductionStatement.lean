import Langlands.GroupScheme.SimplyConnected.SplitPicardInputsStatement

/-! # Reduction of the split semisimple Picard criterion -/

universe u

namespace Langlands.GroupScheme

/-- The character-lifting and Picard-trivial-cover inputs imply the unchanged
split semisimple simple-connectedness/Picard equivalence. -/
def SplitSemisimplePicardReductionStatement : Prop :=
  SplitSemisimplePicardGeometricInputsStatement.{u} →
    SplitSemisimpleSimplyConnectedPicardStatement.{u}

end Langlands.GroupScheme

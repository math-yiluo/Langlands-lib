import Langlands.GroupScheme.IntegralModel.ConditionalReductiveParabolicSpreading
import Langlands.GroupScheme.Reductive.GenericSpreadingProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # Simultaneous good reductive and parabolic spreading: proof -/

universe u

namespace Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading

/-- A number-field connected reductive group and any supplied parabolic inclusion
admit simultaneous good models over one actual finite S-integer ring. -/
theorem existence : ExistenceStatement.{u} :=
  existenceStatement_of_spreadingStatements genericReductivitySpreading parabolicDynamic

end Langlands.GroupScheme.IntegralModel.ReductiveParabolicSpreading

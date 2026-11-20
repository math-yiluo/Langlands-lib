import Langlands.Representation.Plancherel.DynamicOppositeContragredientScalarReduction
import Langlands.Representation.Plancherel.DynamicOppositeDualAdjunctionProof

namespace Langlands.Plancherel

universe u uV

/-- The canonical opposite-intertwiner scalar for the smooth contragredient is
the pullback of the original scalar along inversion of the unramified parameter. -/
theorem conditionalDynamicOppositeContragredientScalar :
    ConditionalDynamicOppositeContragredientScalarStatement.{u, uV} :=
  conditionalDynamicOppositeContragredientScalar_of_dualAdjunction
    conditionalDynamicOppositeDualAdjunction

end Langlands.Plancherel

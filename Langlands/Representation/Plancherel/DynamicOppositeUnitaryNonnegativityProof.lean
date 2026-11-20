import Langlands.Representation.Plancherel.DynamicOppositeUnitaryNonnegativity
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof

namespace Langlands.Plancherel

universe u uV

/-- The canonical opposite-intertwiner scalar is regular with nonnegative real value
at each common regular unitary parameter. -/
theorem conditionalDynamicOppositeUnitaryNonneg :
    ConditionalDynamicOppositeUnitaryNonnegStatement.{u, uV} :=
  conditionalDynamicOppositeUnitaryNonneg_of_hermitianAdjunction
    conditionalDynamicOppositeHermitianAdjunction

end Langlands.Plancherel

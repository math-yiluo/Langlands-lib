import Langlands.Representation.Plancherel.DynamicOppositeUniformNonvanishing
import Langlands.Representation.Plancherel.DynamicOppositeHermitianAdjunctionProof

namespace Langlands.Plancherel

universe u uV

/-- The canonical opposite-intertwiner scalar is nonzero, and it and its inverse
are regular with positive real values at each common regular unitary parameter. -/
theorem conditionalDynamicOppositeUnitaryPositive :
    ConditionalDynamicOppositeUnitaryPositiveStatement.{u, uV} :=
  conditionalDynamicOppositeUnitaryPositive_of_hermitianAdjunction
    conditionalDynamicOppositeHermitianAdjunction

end Langlands.Plancherel

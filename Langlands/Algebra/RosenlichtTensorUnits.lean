import Langlands.Algebra.RosenlichtTensorUnitsReduction
import Langlands.Algebra.RosenlichtBoundedInversePairs

universe u v w

namespace Langlands.Algebra

/-- Rosenlicht splitting of units in the actual tensor product of finite-type domains. -/
theorem rosenlichtTensorUnits : RosenlichtTensorUnitsStatement.{u,v,w} :=
  Rosenlicht.tensorUnits_of_boundedInversePairs Rosenlicht.boundedInversePairs

end Langlands.Algebra

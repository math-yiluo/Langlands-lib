import Langlands.Geometry.Building.KPUnramifiedComparisonRootReduction
import Langlands.Geometry.Building.UnramifiedDoubledRootDepthModelProof

/-! # The root field for concrete unramified apartment lifts -/

universe u

namespace Langlands.Geometry.Building

/-- All seven root-comparison fields hold for every supplied concrete
unramified apartment lift, with uniform depth preserved in the lower block. -/
theorem unramifiedComparisonRootField :
    UnramifiedComparisonRootFieldStatement.{u} :=
  unramifiedComparisonRootField_of_doubledRootDepthModel
    unramifiedDoubledRootDepthModel

end Langlands.Geometry.Building

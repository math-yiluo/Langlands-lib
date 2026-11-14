import Langlands.GroupScheme.RelativeLevi.OppositeBorelFromLieContainment
import Langlands.GroupScheme.RelativeLevi.ParabolicLieContainmentProof

/-! # The unique opposite Borel through a maximal torus -/

universe u

namespace Langlands.GroupScheme

/-- A relative Borel containing the specified maximal torus has a unique
opposite Borel, with equality and intersection on every test scheme. -/
theorem relativeOppositeBorel : RelativeOppositeBorelStatement.{u} :=
  relativeOppositeBorel_of_lieContainment relativeParabolicLieContainment

end Langlands.GroupScheme

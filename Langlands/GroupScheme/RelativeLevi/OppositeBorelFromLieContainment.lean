import Langlands.GroupScheme.RelativeLevi.BorelDynamicPresentationProof
import Langlands.GroupScheme.RelativeLevi.OppositeBorelReduction

/-! # The opposite Borel theorem from the remaining Lie-spreading input -/

universe u

namespace Langlands.GroupScheme

/-- The local construction is discharged; only the explicit
Lie-containment-spreading statement remains as a premise. -/
theorem relativeOppositeBorel_of_lieContainment
    (hLie : RelativeParabolicLieContainmentStatement.{u}) :
    RelativeOppositeBorelStatement.{u} :=
  relativeOppositeBorel_of_localPresentation_and_lieContainment
    relativeBorelDynamicPresentation hLie

end Langlands.GroupScheme

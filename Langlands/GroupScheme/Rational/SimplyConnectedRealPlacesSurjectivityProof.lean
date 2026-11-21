import Langlands.GroupScheme.Rational.RealPlacesToralBridge
import Langlands.GroupScheme.Rational.RealPlacesTorusCohomology
import Langlands.GroupScheme.Rational.SimultaneousRealMaximalTorusApproximation

/-! # Surjectivity of localization at the real places -/

universe u

namespace Langlands.GroupScheme

/-- For a simply connected group over a number field, every family of real-place
cocycles comes from a global cocycle up to twists after finite separable refinement. -/
theorem simplyConnectedRealPlacesSurjectivity :
    SimplyConnectedRealPlacesSurjectivityStatement.{u} :=
  simplyConnectedRealPlacesSurjectivity_of_tori realPlacesToralRepresentatives
    simultaneousRealMaximalTorusApproximation realPlacesTorusCohomologySurjectivity

end Langlands.GroupScheme

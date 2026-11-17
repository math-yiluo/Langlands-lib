import Langlands.Geometry.Building.UnramifiedTorusUnitCoveringReduction
import Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusProof
import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentProof

/-! # Rational translates of Galois-fixed apartment points cover the fixed building -/

universe u

namespace Langlands.Geometry.Building

/-- Every coefficient-fixed building point is a rational translate of the image
of a coefficient-fixed point of the supplied special apartment. -/
theorem unramifiedGaloisFixedBuildingPoint :
    UnramifiedGaloisFixedBuildingPointStatement.{u} :=
  unramifiedTorusUnitCoveringReduction.{u}
    unramifiedFixedPointSplitTorus.{u}
    unramifiedTorusUnitFixedApartment.{u}

end Langlands.Geometry.Building

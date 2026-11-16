import Langlands.Geometry.Building.UnramifiedFixedPointTransporterReduction
import Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentProof

/-! # The split-centralizing transporter of special apartments over the maximal unramified extension -/

universe u

namespace Langlands.Geometry.Building

/-- **KP 9.3.11(1) with 9.3.12 over `K`.** The split-centralizing transporter statement,
obtained by applying the published reduction to the published two-point special-apartment
theorem. -/
theorem unramifiedFixedPointTransporter :
    UnramifiedFixedPointTransporterStatement.{u} :=
  unramifiedFixedPointTransporter_of_fixedPairSpecialApartment
    unramifiedFixedPairSpecialApartment.{u}

end Langlands.Geometry.Building

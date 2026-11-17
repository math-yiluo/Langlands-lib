import Langlands.Geometry.Building.UnramifiedFixedLeviTransportReduction
import Langlands.Geometry.Building.UnramifiedTorusUnitFixedApartmentProof
import Langlands.Geometry.Building.UnramifiedLeviSharpApartmentTransportProof

/-! # Levi transport of Galois-fixed points of the unramified apartment -/

universe u

namespace Langlands.Geometry.Building

/-- Rational normalizer translates of coefficient-fixed apartment points admit a
depth-zero Levi correction whose apartment action is again coefficient-fixed. -/
theorem unramifiedFixedLeviTransport :
    UnramifiedFixedLeviTransportStatement.{u} :=
  unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp
    unramifiedTorusUnitFixedApartment.{u}
    unramifiedLeviSharpApartmentTransport.{u}

end Langlands.Geometry.Building

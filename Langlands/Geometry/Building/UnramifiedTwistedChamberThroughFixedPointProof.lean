import Langlands.Geometry.Building.UnramifiedTwistedChamberThroughFixedPointReduction
import Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientReduction
import Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientProof

/-! # Proof of twisted-stable chambers through a twisted-fixed point -/

universe u

namespace Langlands.Geometry.Building

/-- **Twisted-stable chambers through a twisted-fixed point over the maximal unramified
extension.** The finite-field quotient input `unramifiedTwistedChamberQuotient` gives, via
`unramifiedTwistedGeneratorChamber_of_quotient`, a chamber through the point that is stable
under the twisted action of one dense generator of `Aut(K/F)`; the reduction
`unramifiedTwistedChamberThroughFixedPointReduction` upgrades it to a chamber stable under the
twisted action of all of `Aut(K/F)`. -/
theorem unramifiedTwistedChamberThroughFixedPoint :
    UnramifiedTwistedChamberThroughFixedPointStatement.{u} :=
  unramifiedTwistedChamberThroughFixedPointReduction
    (unramifiedTwistedGeneratorChamber_of_quotient unramifiedTwistedChamberQuotient)

end Langlands.Geometry.Building

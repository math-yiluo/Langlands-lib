import Langlands.Geometry.Building.UnramifiedTwistedChamberQuotientResidueReduction
import Langlands.Geometry.Building.UnramifiedTwistedResidueQuotientProof

/-! # Proof of the finite-field quotient input for a twisted chamber through a fixed point -/

universe u

namespace Langlands.Geometry.Building

/-- The finite-field quotient input for a twisted chamber through a twisted-fixed point.
The published conditional reduction `unramifiedTwistedChamberQuotientResidueReduction`
(residue quotient for every Frobenius lift implies the target) is applied to the published
proof `unramifiedTwistedResidueQuotient` of the residue quotient statement. -/
theorem unramifiedTwistedChamberQuotient : UnramifiedTwistedChamberQuotientStatement.{u} :=
  unramifiedTwistedChamberQuotientResidueReduction unramifiedTwistedResidueQuotient

end Langlands.Geometry.Building

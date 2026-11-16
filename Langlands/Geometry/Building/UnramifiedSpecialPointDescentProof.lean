import Langlands.Geometry.Building.UnramifiedSpecialPointRootJumpReduction
import Langlands.Geometry.Building.UnramifiedRootJumpDescentProof

/-! # Proof that special points descend from the unramified building -/

universe u

namespace Langlands.Geometry.Building

/-- Special points descend by the root-jump reduction and the unconditional
unramified root-jump theorem. -/
theorem unramifiedSpecialPointDescent :
    UnramifiedSpecialPointDescentStatement.{u} :=
  unramifiedSpecialPointRootJumpReduction unramifiedRootJumpDescent

end Langlands.Geometry.Building

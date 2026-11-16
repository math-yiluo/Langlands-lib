import Langlands.Geometry.Building.UnramifiedRootSpecializationProof

/-! # Proof of unramified descent of vanishing root directions -/

universe u

namespace Langlands.Geometry.Building

/-- Structural unramified root specialization and the actual residue-root
lifting reduction give the published root-jump descent statement. -/
theorem unramifiedRootJumpDescent :
    UnramifiedRootJumpDescentStatement.{u} :=
  unramifiedRootJumpDescent_of_rootSpecialization unramifiedRootSpecialization

end Langlands.Geometry.Building

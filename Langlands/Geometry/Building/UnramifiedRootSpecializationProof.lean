import Langlands.Geometry.Building.UnramifiedRootSpecializationReduction
import Langlands.Geometry.Building.UnramifiedFixedResidueRootModelProof

/-! # Proof of structural unramified root specialization -/

universe u

namespace Langlands.Geometry.Building

/-- **Structural unramified root specialization.** The published reduction
`unramifiedRootSpecialization_of_fixedResidueRootModel`, applied to the published
proof `unramifiedFixedResidueRootModel` of the fixed-point residue-root model
statement. -/
theorem unramifiedRootSpecialization :
    UnramifiedRootSpecializationStatement.{u} :=
  unramifiedRootSpecialization_of_fixedResidueRootModel unramifiedFixedResidueRootModel

end Langlands.Geometry.Building

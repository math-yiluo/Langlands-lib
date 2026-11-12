import Langlands.AbelianScheme.Tate.GeometricTorsionRankStatement
import Langlands.AbelianScheme.Tate.GeometricTorsionRankAssembly
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof
import Langlands.AbelianScheme.FieldCubePullbackProof

/-! # Rank and cardinality of actual geometric torsion -/

universe u

namespace Langlands.AbelianScheme.Tate

/-- Actual geometric torsion at every positive invertible level is a free
residue module of rank twice the specified relative dimension, with cardinality
the level raised to that rank. -/
theorem geometricTorsionRank : GeometricTorsionRankStatement.{u} :=
  geometricTorsionRank_of_ample_and_cube
    Langlands.GroupScheme.algebraicallyClosedFieldAmpleExistence.{u}
    Langlands.GroupScheme.fieldCubePullback.{u}

end Langlands.AbelianScheme.Tate

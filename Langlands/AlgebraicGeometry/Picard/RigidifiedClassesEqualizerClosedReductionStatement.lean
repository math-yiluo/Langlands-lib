import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesEqualizerClosedAffineStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesZariskiSeparatedStatement

/-! # Reduction of the closed agreement locus to an affine base -/

universe u

namespace Langlands.AbelianScheme

/-- The closed agreement locus over an affine base with identity parameter, together with
Zariski separatedness of actual rigidified classes, implies the closed agreement locus for an
arbitrary base `S` and parameter `T`. -/
def RigidifiedClassesEqualizerClosedReductionStatement : Prop :=
  RigidifiedClassesEqualizerClosedAffineStatement.{u} →
    RigidifiedClassesZariskiSeparatedStatement.{u} →
      RigidifiedClassesEqualizerClosedStatement.{u}

end Langlands.AbelianScheme

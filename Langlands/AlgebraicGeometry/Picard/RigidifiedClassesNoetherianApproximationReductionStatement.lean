import Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationStatement

/-! # Reduction of noetherian approximation of agreement to noetherian models -/

universe u

namespace Langlands.AbelianScheme

/-- Existence of noetherian models of abelian schemes over an affine base together with two
rigidified line bundles implies noetherian approximation of the agreement of two rigidified
classes. -/
def RigidifiedClassesNoetherianApproximationReductionStatement : Prop :=
  AbelianSchemeNoetherianModelStatement.{u} →
    RigidifiedClassesNoetherianApproximationStatement.{u}

end Langlands.AbelianScheme

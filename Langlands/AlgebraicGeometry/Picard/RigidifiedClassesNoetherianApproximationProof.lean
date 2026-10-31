import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationReductionProof
import Langlands.AlgebraicGeometry.Picard.AbelianSchemeNoetherianModelProof
import Langlands.AbelianScheme.SubalgebraDescentProof
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SchemeSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SmoothSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsSeparatedSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsProperSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.GeometricallyConnectedSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleIsoSubalgebraDescentProof

/-! # Noetherian approximation of the agreement of two rigidified classes -/

universe u

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Two rigidified classes on an abelian scheme over an affine base that agree after base change
already agree over a noetherian model. -/
theorem rigidifiedClassesNoetherianApproximation :
    RigidifiedClassesNoetherianApproximationStatement.{u} :=
  rigidifiedClassesNoetherianApproximationReduction
    (abelianSchemeNoetherianModelReduction
      (subalgebraDescentReduction schemeSubalgebraDescent GroupScheme.subalgebraDescent
        isSeparatedSubalgebraDescent isProperSubalgebraDescent smoothSubalgebraDescent
        geometricallyConnectedSubalgebraDescent)
      lineBundleSubalgebraDescent lineBundleIsoSubalgebraDescent)

end Langlands.AbelianScheme

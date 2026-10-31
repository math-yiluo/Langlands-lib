import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsNoetherianReduction
import Langlands.AlgebraicGeometry.Modules.NoetherianUniversalPerfectSectionsProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.IsProperSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleSubalgebraDescentProof

/-! # Universal perfect representatives for smooth proper line-bundle sections: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Modules

/-- Actual derived sections of a line bundle on a smooth proper family over an
arbitrary affine base admit one strictly perfect representative computing every
affine scalar change. -/
theorem universalPerfectSections : UniversalPerfectSectionsStatement.{u} :=
  universalPerfectSectionsNoetherianReduction
    NoetherianApproximation.isProperSubalgebraDescent
    NoetherianApproximation.lineBundleSubalgebraDescent
    noetherianUniversalPerfectSections

end Langlands.AlgebraicGeometry.Modules

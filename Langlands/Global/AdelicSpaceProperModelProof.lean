import Langlands.Global.AdelicSpaceProperInputsStatement
import Langlands.Global.AdelicSpaceProperModelReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescentProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitPropertyDescentProof

/-! # Proper arithmetic models of proper field morphisms of algebraic spaces -/

universe u

open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

/-- Proper arithmetic model replacement in both global-field characteristics. -/
theorem adelicSpaceProperModel : AdelicSpaceProperModelStatement.{u} :=
  AdelicSpaceProperModelReduction.adelicSpaceProperModel_of_descent.{u}
    spaceLimitMorphismDescent.{u} (spaceLimitPropertyDescent.{u}).2.2.1

end Langlands.Global

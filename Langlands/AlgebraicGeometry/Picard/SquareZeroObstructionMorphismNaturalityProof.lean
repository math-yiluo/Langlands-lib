import Langlands.AlgebraicGeometry.Modules.RelativeAbelianSheafCohomologyPullbackProof
import Langlands.AlgebraicGeometry.Picard.SquareZeroMorphismRelativeComparison

/-! # Proof of naturality of square-zero Picard obstructions under morphisms of thickenings -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Square-zero Picard obstructions are natural under morphisms of thickenings: the obstruction
of `g^* y` is the image of the obstruction of `y` under the cohomology pullback followed by the
adjoint of the ideal map. This combines the published reduction to the relative comparison of
module cohomology with arbitrary pullback, and the proof of that comparison. -/
theorem squareZeroObstructionMorphismNaturality :
    SquareZeroObstructionMorphismNaturalityStatement.{u} :=
  SquareZeroMorphismRelativeComparison.squareZeroObstructionMorphismNaturality_of_relativeComparison
    Modules.AbelianSheafComparison.relativeAbelianSheafCohomologyPullback

end Langlands.AlgebraicGeometry.Picard

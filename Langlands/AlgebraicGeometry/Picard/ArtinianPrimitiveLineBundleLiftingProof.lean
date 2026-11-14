import Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingFromPrerequisites
import Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityProof
import Langlands.AlgebraicGeometry.Picard.ArtinianH2PrimitiveInjectivityProof

/-! # Lifting primitive line bundles along elementary Artinian thickenings -/

universe u

namespace Langlands.AbelianScheme

/-- Let `φ : B' → B` be a surjection of local Artinian rings whose kernel is killed by the
maximal ideal of `B'`, and let `A` be an abelian scheme over `Spec B'` with base change `A₀`
over `Spec B`. A line bundle on `A₀` whose multiplication pullback is isomorphic to the
tensor product of its two projection pullbacks lifts to a line bundle on `A`. -/
theorem artinianPrimitiveLineBundleLifting :
    ArtinianPrimitiveLineBundleLiftingStatement.{u} :=
  artinianPrimitiveLineBundleLiftingReduction
    Langlands.AlgebraicGeometry.Picard.squareZeroObstructionMorphismNaturality
    artinianH2PrimitiveInjectivity

end Langlands.AbelianScheme

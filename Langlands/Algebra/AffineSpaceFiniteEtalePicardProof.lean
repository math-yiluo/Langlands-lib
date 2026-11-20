import Langlands.Algebra.AffineSpaceFiniteEtalePicardReduction
import Langlands.Algebra.AffineSpaceFiniteEtalePolynomialProductProof

/-! # Picard triviality for finite étale covers of affine space -/

namespace Langlands.Algebra

universe u

/-- Every finite étale cover of affine space over a characteristic-zero field has
trivial Picard group. -/
theorem affineSpaceFiniteEtalePicardTrivial :
    AffineSpaceFiniteEtalePicardTrivialStatement.{u} :=
  affineSpaceFiniteEtalePicardTrivial_of_polynomialProduct affineSpaceFiniteEtalePolynomialProduct

end Langlands.Algebra

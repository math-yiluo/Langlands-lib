import Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardAssembly
import Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof
import Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof

/-! # The fppf Picard sheaf of an abelian scheme over a finite-type `ℤ`-algebra: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- The actual fppf Picard class sheaf of every abelian scheme over `Spec R`, for a
commutative ring `R` of finite type over `ℤ`, is an algebraic space with a surjective
etale scheme atlas locally of finite presentation over `Spec R`. The published
conditional assembly is applied to the published proofs of its two versal inputs. -/
theorem finiteTypeAbelianPicardSheafAlgebraicSpace :
    FiniteTypeAbelianPicardSheafAlgebraicSpaceStatement.{u} :=
  finiteTypeAbelianPicardSheafAlgebraicSpace_of_versalInputs finiteTypeFormalVersalBundle
    CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation

end Langlands.AlgebraicGeometry.Picard

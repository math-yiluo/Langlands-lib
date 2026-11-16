import Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationReduction
import Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof

/-! # Algebraization of formally versal Picard families: proof -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Algebraization of a formally versal line bundle over a complete local base, for
proper flat schemes over finite-type `ℤ`-algebras. The published reduction applies to
the published etale approximation theorem over finite-type `ℤ`-algebras. -/
theorem versalAlgebraization : VersalAlgebraizationStatement.{u} :=
  versalAlgebraization_of_etaleApproximation
    CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation

end Langlands.AlgebraicGeometry.Picard

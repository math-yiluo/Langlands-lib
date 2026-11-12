import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricFibreComponentsStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricComponentApproximation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitModelExistenceQuasiSeparatedReduction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationLimitModelProof

/-! # Constructibility of the number of geometric connected components

Conrad's Lemma 5.1 follows from the actual Noetherian approximation construction
and finite-stage descent of étale scheme equivalence relations.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Conrad's Lemma 5.1 over an arbitrary commutative ring. -/
theorem geometricFibreComponentsConstructible :
    GeometricFibreComponentsConstructibleStatement.{u} :=
  geometricFibreComponentsConstructible_of_limitModels
    (SpaceLimitModelExistenceQuasiSeparatedReduction.spaceLimitModelExistenceQuasiSeparated_of_relation
      EtaleEquivalenceRelation.limitModelExistence)

end Langlands.AlgebraicGeometry.AlgebraicSpace

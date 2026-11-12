import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitModelExistenceQuasiSeparatedReduction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationLimitModelProof

/-! # Model existence for quasi-separated algebraic spaces along affine limits -/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A quasi-separated algebraic space of finite presentation over a cofiltered
affine limit has a quasi-separated model of finite presentation at some stage. -/
theorem spaceLimitModelExistenceQuasiSeparated :
    SpaceLimitModelExistenceQuasiSeparated.{u} :=
  SpaceLimitModelExistenceQuasiSeparatedReduction.spaceLimitModelExistenceQuasiSeparated_of_relation
    EtaleEquivalenceRelation.limitModelExistence

end Langlands.AlgebraicGeometry.AlgebraicSpace

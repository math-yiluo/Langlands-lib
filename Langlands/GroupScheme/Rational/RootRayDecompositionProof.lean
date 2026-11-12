import Langlands.GroupScheme.Rational.RootRayDecomposition
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Finite disjoint rays of actual positive relative roots: proof -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- For every connected reductive group over any field, maximal split torus and
cocharacter, the indivisible positive actual roots are finitely enumerated, their
positive integral rays are pairwise disjoint, and an actual root is positive
exactly when it lies on one of these rays. The published rank-one factorization
gives the relative root system, which feeds the published ray reduction. -/
theorem relativeRootRayDecomposition : RelativeRootRayDecompositionStatement.{u} :=
  relativeRootRayDecompositionStatement_of_relativeRootSystemStatement
    (relativeRootSystemStatement_of_rootRankOneFactorizationStatement
      rootRankOneFactorization)

end Langlands.GroupScheme.RelativeRoot

import Langlands.GroupScheme.Rational.RootSubgroupVectorReduction
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.SemigroupCommutatorProof
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.CyclicWeightFiltrationProof

/-! # Proof of the vector and central quotient structure of relative root subgroups -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- **Relative root subgroups are vector groups up to a central doubled-root
quotient** (KP §2.6.8 and Proposition 2.11.14, CGP Lemma 3.3.8). For every
actual relative root `a` of a maximal split torus in a connected reductive
group over any field: if `2a` is not a relative root, every representative of
`Uₐ` is a vector group; if `2a` is a relative root, `U₂ₐ ≤ Uₐ`, the points of
`U₂ₐ` commute with those of `Uₐ` on every test, and every representative of
`Uₐ` has a represented fppf quotient by `U₂ₐ` which is a vector group. -/
theorem rootSubgroupVector : RootSubgroupVectorStatement.{u} :=
  rootSubgroupVectorReduction
    (relativeRootSystemStatement_of_rootRankOneFactorizationStatement
      rootRankOneFactorization)
    semigroupRealization semigroupCommutator cyclicRootFunctorComparison
    cyclicWeightFiltration

end Langlands.GroupScheme.RelativeRoot

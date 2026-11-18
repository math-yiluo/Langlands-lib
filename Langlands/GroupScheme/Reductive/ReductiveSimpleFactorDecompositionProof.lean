import Langlands.GroupScheme.Reductive.ReductiveSimpleFactorDecompositionReduction
import Langlands.GroupScheme.Reductive.SimpleFactorDecompositionProof

/-! # The simple factors of a connected reductive group over a field: proof -/

universe u

namespace Langlands.GroupScheme

/-- Conrad, *Reductive group schemes*, Exercise 5.5.2: the reductive simple-factor
decomposition over a field. It follows from the semisimple decomposition theorem
(Theorem 5.1.19, `simpleFactorDecomposition`) by `reductiveSimpleFactorDecomposition_reduction`. -/
theorem reductiveSimpleFactorDecomposition : ReductiveSimpleFactorDecompositionStatement.{u} :=
  reductiveSimpleFactorDecomposition_reduction simpleFactorDecomposition

end Langlands.GroupScheme

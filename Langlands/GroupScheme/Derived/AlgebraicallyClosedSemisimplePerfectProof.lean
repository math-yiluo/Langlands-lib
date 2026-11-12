import Langlands.GroupScheme.Derived.SemisimplePerfectGeneration
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.Reductive.TorusGenerationProof

/-! # algebraicallyClosedSemisimplePerfect: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Every semisimple group over an algebraically closed field has full derived subgroup functor. -/
theorem algebraicallyClosedSemisimplePerfect :
    AlgebraicallyClosedSemisimplePerfectStatement.{u} :=
  algebraicallyClosedSemisimplePerfect_of_maximalTorusDerived_of_torusGeneration
    algebraicallyClosedSemisimpleMaximalTorusDerived reductiveFiniteTorusGeneration

end Langlands.GroupScheme

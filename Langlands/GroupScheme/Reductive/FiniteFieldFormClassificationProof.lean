import Langlands.GroupScheme.Reductive.FiniteFieldFormClassificationReduction
import Langlands.GroupScheme.Reductive.FiniteFieldFormExistenceProof
import Langlands.GroupScheme.Reductive.InnerFormStarActionProof

/-! # Classification of forms of a split reductive group over a finite field -/

universe u

namespace Langlands.GroupScheme

/-- **Forms over a finite field.** Every finite-order based automorphism of the based root
datum is the class of some form, and two forms are isomorphic over the finite field exactly
when their classes are conjugate. -/
theorem finiteFieldFormClassification : FiniteFieldFormClassificationStatement.{u} :=
  finiteFieldFormClassification_of_innerFormStarAction innerFormStarAction
    finiteFieldFormExistence

end Langlands.GroupScheme

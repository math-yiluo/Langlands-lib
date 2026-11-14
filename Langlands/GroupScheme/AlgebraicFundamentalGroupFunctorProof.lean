import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctorLaws
import Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupMapNaturality

/-! # Functoriality of the algebraic fundamental group -/

noncomputable section

universe u

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

/-- **Functoriality of the algebraic fundamental group** (Kaletha–Prasad,
Lemma 11.3.6): selected maps preserve identities and composition for all
quotient presentations over every field and separable closure. -/
theorem algebraicFundamentalGroupFunctor :
    AlgebraicFundamentalGroupFunctorStatement.{u} :=
  algebraicFundamentalGroupFunctor_of_map_and_comparison
    (algebraicFundamentalGroupMap_of_comparison algebraicFundamentalGroupComparison)
    algebraicFundamentalGroupComparison

end Langlands.GroupScheme.AlgebraicFundamentalGroup

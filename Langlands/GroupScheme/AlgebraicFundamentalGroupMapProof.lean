import Langlands.GroupScheme.AlgebraicFundamentalGroupMapNaturality
import Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof

/-! # Induced Galois maps on algebraic fundamental groups -/

universe u

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

/-- **Induced maps on algebraic fundamental groups** (Kaletha–Prasad,
Lemma 11.3.6): every morphism of connected reductive groups induces a unique
integral map satisfying every torus factorization law. The selected map is
Galois equivariant and compatible with all changes of quotient presentations. -/
theorem algebraicFundamentalGroupMap :
    AlgebraicFundamentalGroupMapStatement.{u} :=
  algebraicFundamentalGroupMap_of_comparison algebraicFundamentalGroupComparison

end Langlands.GroupScheme.AlgebraicFundamentalGroup

import Langlands.GroupScheme.AlgebraicFundamentalGroupConjugators
import Langlands.GroupScheme.AlgebraicFundamentalGroupConjugatorExistence
import Langlands.GroupScheme.AlgebraicFundamentalGroupCorootTransport
import Langlands.GroupScheme.AlgebraicFundamentalGroupWeyl

/-! # Canonical coherent Galois comparisons for the algebraic fundamental group -/

noncomputable section

universe u

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

/-- **Canonical comparisons of the algebraic fundamental group** (Kaletha–Prasad,
Construction 11.3.1). For a connected reductive group over a field and a separable closure,
any two torus/cover presentations have a unique canonical comparison; it is bijective,
Galois equivariant, given by every geometric conjugator, and satisfies the identity and
composition laws. -/
theorem algebraicFundamentalGroupComparison :
    AlgebraicFundamentalGroupComparisonStatement.{u} := by
  intro k E _ _ _ _ G hG
  exact Choice.comparison_of_conjugators E
    (Choice.exists_isConjugationComparison E hG)
    (fun _ _ _ _ h => h.corootImage_le)
    (fun _ _ _ h => h.sub_mem_corootImage hG)
    (fun _ _ _ _ h σ => h.exists_galois σ)

end Langlands.GroupScheme.AlgebraicFundamentalGroup

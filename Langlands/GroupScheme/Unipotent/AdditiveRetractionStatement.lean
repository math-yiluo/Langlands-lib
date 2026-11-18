import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Copies of `𝔾ₐ` in elementary unipotent groups are direct factors (Milne 14.47) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 14.47: over a field `k` of characteristic `p > 0`, let `G` be
elementary unipotent (some homomorphism `e` from `G` to a vector group `𝔾ₐⁿ` is a closed
immersion). Every closed subgroup of `G` isomorphic to `𝔾ₐ` is a direct factor: for every
homomorphism `i : 𝔾ₐ ⟶ G` that is a closed immersion there is a homomorphism `r : G ⟶ 𝔾ₐ`
with `i ≫ r = 𝟙`. -/
def ElementaryUnipotentAdditiveRetractionStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k))) (n : ℕ)
    (e : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) n), IsClosedSubgroup e →
    ∀ i : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G, IsClosedSubgroup i →
      ∃ r : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1, i ≫ r = 𝟙 _

end Langlands.GroupScheme

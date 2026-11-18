import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Split elementary unipotent groups are vector groups (Milne 14.64) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, 14.64: over a field `k` of characteristic `p > 0`, an elementary unipotent
group `G` (some homomorphism `e` from `G` to a vector group `𝔾ₐⁿ` is a closed immersion) is
split if and only if it is isomorphic to `𝔾ₐʳ` for some `r`. -/
def ElementaryUnipotentSplitIffVectorStatement : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k))) (n : ℕ)
    (e : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) n), IsClosedSubgroup e →
    (RelativeRoot.IsSplitUnipotent G ↔
      ∃ r : ℕ, Nonempty (G ≅ VectorGroup.groupScheme (CommRingCat.of k) r))

end Langlands.GroupScheme

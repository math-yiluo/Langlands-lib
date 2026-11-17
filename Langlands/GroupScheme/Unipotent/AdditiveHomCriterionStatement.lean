import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Unipotence through homomorphisms to the additive group (Milne 14.22) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 14.22: an affine algebraic group `G` over a field `k` is unipotent if
and only if every nontrivial closed subgroup of `G` admits a nontrivial homomorphism to the
additive group `𝔾ₐ = VectorGroup.groupScheme k 1`. -/
def UnipotentAdditiveHomCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    IsUnipotent G ↔
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G), IsClosedSubgroup i →
        SubgroupFunctor.range i ≠ ⊥ →
          Nontrivial (H ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)

end Langlands.GroupScheme

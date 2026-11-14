import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.SplitSolvable

/-! # Statement: split Borel subgroups over an arbitrary field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 17.105(a),(b). Let `G` be a smooth affine group over a field `k` (a group
variety, not necessarily connected) and let `b : B ⟶ G` be a split Borel subgroup: a geometric
Borel subgroup with `B` split solvable.
* (a) Every closed subgroup `h : H ⟶ G` with `H` split solvable is contained in a conjugate of
  `B` by a `k`-point of `G`.
* (b) Every split Borel subgroup of `G` is a conjugate of `B` by a `k`-point of `G`. -/
def SplitSolvableBorelConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
    IsGeometricBorelSubgroup b → IsSplitSolvableGroupScheme B →
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsClosedSubgroup h → IsSplitSolvableGroupScheme H →
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
            SubgroupFunctor.range h ≤ SubgroupFunctor.range (b ≫ (G.innerIso g).hom)) ∧
      ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ G),
        IsGeometricBorelSubgroup b' → IsSplitSolvableGroupScheme B' →
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
            SubgroupFunctor.range (b ≫ (G.innerIso g).hom) = SubgroupFunctor.range b'

end Langlands.GroupScheme

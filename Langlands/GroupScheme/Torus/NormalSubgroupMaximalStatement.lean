import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: maximal tori of a normal subgroup variety -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 17.85. Let `G` be a smooth connected affine group over a field `k` and let
`n : N ⟶ G` be a smooth closed normal subgroup.
* For every maximal torus `T` of `G`, the largest subtorus `(T ∩ N)_t` of `T ∩ N` is a maximal
  torus of `N`. Equivalently, `N` has a maximal torus contained in `T`.
* Every maximal torus `S` of `N` is of this form. Equivalently, `S` lies in a maximal torus of
  `G`. -/
def NormalSubgroupMaximalTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
    IsClosedSubgroup n → Smooth N.X.hom → (SubgroupFunctor.range n).IsNormal →
      (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
        ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ N),
          IsMaximalTorus s ∧ SubgroupFunctor.range (s ≫ n) ≤ SubgroupFunctor.range j) ∧
      (∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ N), IsMaximalTorus s →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsMaximalTorus j ∧ SubgroupFunctor.range (s ≫ n) ≤ SubgroupFunctor.range j)

end Langlands.GroupScheme

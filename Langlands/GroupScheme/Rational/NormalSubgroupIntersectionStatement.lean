import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Intersections with maximal tori, parabolic and Borel subgroups over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Conrad, *Reductive group schemes*, Exercise 5.5.1(i)–(iii). Let `G` be a smooth connected
affine group over a field `k`.

* For a maximal `k`-torus `t : T ⟶ G` and a smooth connected closed `k`-subgroup `n : N ⟶ G`
  normalized by `T`, the scheme-theoretic intersection `T ∩ N` is a maximal `k`-torus of `N`.
* For a smooth connected normal closed `k`-subgroup `h : H ⟶ G` and a parabolic `k`-subgroup
  `p : P ⟶ G`, the scheme-theoretic intersection `P ∩ H` is a connected parabolic `k`-subgroup
  of `H`.
* For `H` as above and a Borel `k`-subgroup `b : B ⟶ G` (one whose base change to `k̄` is a Borel
  subgroup), the scheme-theoretic intersection `B ∩ H` is a Borel `k`-subgroup of `H`.

Each intersection is the subgroup functor `range h ⊓ range p` (and similarly), and the
conclusion supplies a closed subgroup of the smaller group representing it. -/
def NormalSubgroupIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
    (∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
      IsMaximalTorus t →
      ∀ (N : GroupScheme (Spec (CommRingCat.of k))) (n : N ⟶ G),
        IsClosedSubgroup n → Smooth N.X.hom → ConnectedSpace N.X.left →
        (SubgroupFunctor.range n).IsNormalizedBy (SubgroupFunctor.range t) →
        ∃ (C : CommGroupScheme (Spec (CommRingCat.of k))) (c : C.toGrp ⟶ N),
          IsMaximalTorus c ∧
            SubgroupFunctor.range (c ≫ n) =
              SubgroupFunctor.range n ⊓ SubgroupFunctor.range t) ∧
    ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
      IsClosedSubgroup h → Smooth H.X.hom → ConnectedSpace H.X.left →
      (SubgroupFunctor.range h).IsNormal →
      (∀ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G),
        IsParabolicSubgroup p →
        ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : Q ⟶ H),
          IsParabolicSubgroup q ∧ ConnectedSpace Q.X.left ∧
            SubgroupFunctor.range (q ≫ h) =
              SubgroupFunctor.range h ⊓ SubgroupFunctor.range p) ∧
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsGeometricBorelSubgroup b →
        ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ H),
          IsGeometricBorelSubgroup c ∧
            SubgroupFunctor.range (c ≫ h) =
              SubgroupFunctor.range h ⊓ SubgroupFunctor.range b

end Langlands.GroupScheme

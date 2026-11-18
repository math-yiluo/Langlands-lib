import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The multiplicative part of a commutative algebraic group (Milne 16.17) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Note 16.17 and the remark after the proof of Theorem 16.13. Let `G` be a
commutative affine algebraic group over a field `k`, with a closed subgroup `s : S ⟶ G` of
multiplicative type and an fppf quotient `q : G ⟶ Q` by it onto a unipotent group (property
16.17(b)). Then:
* (16.17(a)) `S` contains every closed subgroup of multiplicative type;
* (16.17(c)) `S` is contained in every closed subgroup `H` admitting an fppf quotient
  `G ⟶ Q'` by `H` onto a unipotent group;
* (base change) for every field extension `K` of `k`, `S_K` is of multiplicative type and
  contains every closed subgroup of multiplicative type of `G_K`;
* (p.329) if `G` is smooth then `S` is smooth, and if `G` is connected then `S` is connected. -/
def CommutativeMultiplicativePartCharacterizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X]
    (S Q : GroupScheme (Spec (CommRingCat.of k))) (s : S ⟶ G) (q : G ⟶ Q),
    IsClosedSubgroup s → IsMultiplicativeType S →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q → IsUnipotent Q →
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsClosedSubgroup h → IsMultiplicativeType H →
          SubgroupFunctor.range h ≤ SubgroupFunctor.range s) ∧
      (∀ (H Q' : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G) (q' : G ⟶ Q'),
        IsClosedSubgroup h → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range h) q' →
          IsUnipotent Q' → SubgroupFunctor.range s ≤ SubgroupFunctor.range h) ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        let F := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        IsMultiplicativeType (F.obj S) ∧
          ∀ (H : GroupScheme (Spec (CommRingCat.of K))) (h : H ⟶ F.obj G),
            IsClosedSubgroup h → IsMultiplicativeType H →
              SubgroupFunctor.range h ≤ SubgroupFunctor.range (F.map s)) ∧
      (Smooth G.X.hom → Smooth S.X.hom) ∧
      (ConnectedSpace G.X.left → ConnectedSpace S.X.left)

end Langlands.GroupScheme

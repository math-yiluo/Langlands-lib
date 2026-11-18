import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The unipotent part of an extension of a multiplicative group (Milne 16.8, 16.10) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Notes 16.8 and 16.10. Let `G` be an affine algebraic group over a field `k` with a
normal unipotent closed subgroup `i : U ⟶ G` and an fppf quotient `q : G ⟶ M` by it onto a group
of multiplicative type (the conditions of Theorem 16.6(b); `U` is Milne's `G_u`). Then:
* (16.8(c)) `U` is contained in every normal closed subgroup `N` of `G` admitting an fppf
  quotient `G ⟶ M'` by `N` onto a group of multiplicative type;
* (16.8, base change) for every field extension `K` of `k`, the base change `U_K` is unipotent
  and contains every unipotent closed subgroup of `G_K`;
* (16.10) if `G` is smooth then `U` is smooth, and if `G` is connected then `U` is connected. -/
def MultiplicativeExtensionUnipotentPartStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (U M : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G) (q : G ⟶ M),
    IsClosedSubgroup i → IsUnipotent U → (SubgroupFunctor.range i).IsNormal →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q → IsMultiplicativeType M →
      (∀ (N M' : GroupScheme (Spec (CommRingCat.of k))) (j : N ⟶ G) (q' : G ⟶ M'),
        IsClosedSubgroup j → (SubgroupFunctor.range j).IsNormal →
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q' → IsMultiplicativeType M' →
            SubgroupFunctor.range i ≤ SubgroupFunctor.range j) ∧
      (∀ (K : Type u) [Field K] [Algebra k K],
        let F := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        IsUnipotent (F.obj U) ∧
          ∀ (V : GroupScheme (Spec (CommRingCat.of K))) (j : V ⟶ F.obj G),
            IsClosedSubgroup j → IsUnipotent V →
              SubgroupFunctor.range j ≤ SubgroupFunctor.range (F.map i)) ∧
      (Smooth G.X.hom → Smooth U.X.hom) ∧
      (ConnectedSpace G.X.left → ConnectedSpace U.X.left)

end Langlands.GroupScheme

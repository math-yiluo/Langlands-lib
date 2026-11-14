import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: connected groups act trivially on central extensions of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Rigidity for central extensions of groups of multiplicative type** (Milne, *Algebraic
Groups* (2017), Corollary 12.41, with the hypothesis "N central" of the author's errata).
Let `k` be a field, `G` a connected algebraic group over `k`, `H` an algebraic group over `k`,
`j : N ⟶ H` a closed central subgroup and `p : H ⟶ Q` a quotient of `H` by `N`, with `N` and
`Q` of multiplicative type. Every action of `G` on `H` by group automorphisms that maps the
points of `N` to points of `N` is trivial. -/
def MultiplicativeTypeExtensionActionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H N Q : GroupScheme (Spec (CommRingCat.of k)))
    (j : N ⟶ H) (p : H ⟶ Q),
    LocallyOfFiniteType G.X.hom → QuasiCompact G.X.hom → ConnectedSpace G.X.left →
    LocallyOfFiniteType H.X.hom → QuasiCompact H.X.hom →
    IsClosedSubgroup j → IsCentral j → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) p →
    IsMultiplicativeType N → IsMultiplicativeType Q →
      ∀ a : AutomorphicAction G H,
        (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
          x ∈ (SubgroupFunctor.range j).carrier T →
            a.act g x ∈ (SubgroupFunctor.range j).carrier T) →
        ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X), a.act g x = x

end Langlands.GroupScheme

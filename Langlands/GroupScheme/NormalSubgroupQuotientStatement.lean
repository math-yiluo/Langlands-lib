import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: quotients of smooth affine groups by normal closed subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 5.14 with Proposition 5.18 and Corollary 5.26, for smooth affine groups: a
normal closed subgroup `i : N ⟶ G` of a smooth affine group scheme over a field is the kernel of
an fppf quotient map `q : G ⟶ Q` onto a smooth affine group scheme. -/
def NormalSubgroupQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
    IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q

end Langlands.GroupScheme

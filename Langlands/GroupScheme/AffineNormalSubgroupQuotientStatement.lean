import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: quotients of affine algebraic groups by normal closed subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 5.14 with Proposition 5.18: a normal closed subgroup `i : N ⟶ G` of an affine
group scheme locally of finite type over a field is the kernel of an fppf quotient map
`q : G ⟶ Q` onto an affine group scheme locally of finite type. No smoothness, connectedness or
reducedness is assumed of `G` or `N`. -/
def AffineNormalSubgroupQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
    IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        LocallyOfFiniteType Q.X.hom ∧ IsAffineHom Q.X.hom ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q

end Langlands.GroupScheme

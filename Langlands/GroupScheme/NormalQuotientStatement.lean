import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: quotients of affine algebraic groups by normal closed subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every normal closed subgroup of an affine group scheme of finite type over a
field is the actual kernel of an fppf homomorphism onto an affine group scheme of
finite type: the quotient map is flat, surjective and locally of finite
presentation, and its scheme kernel has exactly the points of the subgroup on
every test scheme. -/
def NormalSubgroupQuotientExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
    IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom →
    IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
      ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
        IsAffineHom Q.X.hom ∧ LocallyOfFiniteType Q.X.hom ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q

end Langlands.GroupScheme

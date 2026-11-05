import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: quotients of connected reductive groups by central subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Central quotients are reductive** (derived; see Milne 6.46, 14.18, 14.21 and 16.48). Let
`G` be a connected reductive group over a field and `N` a subgroup functor of `G` contained in
the centre of `G`. Then the target of every fppf homomorphism from `G` onto an affine group
scheme locally of finite type, whose actual scheme kernel has range `N` on every test scheme,
is connected reductive. -/
def CentralQuotientReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q)
    (N : SubgroupFunctor G),
    IsConnectedReductive G → IsAffineHom Q.X.hom → LocallyOfFiniteType Q.X.hom →
    N ≤ center G → RelativeRoot.IsFppfQuotient N q →
      IsConnectedReductive Q

end Langlands.GroupScheme

import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: the quotient of a connected reductive group by its centre -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The target of every fppf homomorphism from a connected reductive group over a
field onto an affine group scheme of finite type, whose actual scheme kernel is
the full scheme-theoretic centre on every test scheme, is connected reductive. -/
def CenterQuotientReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
    IsConnectedReductive G → IsAffineHom Q.X.hom → LocallyOfFiniteType Q.X.hom →
    RelativeRoot.IsFppfQuotient (center G) q →
      IsConnectedReductive Q

/-- For the same homomorphisms, the scheme-theoretic centre of the target is
trivial on every test scheme. -/
def CenterQuotientCenterTrivialStatement : Prop :=
  ∀ (k : Type u) [Field k] (G Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
    IsConnectedReductive G → IsAffineHom Q.X.hom → LocallyOfFiniteType Q.X.hom →
    RelativeRoot.IsFppfQuotient (center G) q →
      center Q = ⊥

end Langlands.GroupScheme

import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.MultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Normal multiplicative and unipotent subgroups with complementary quotients (Milne 16.44) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Lemma 16.44: let `G` be an affine algebraic group over a field `k`, and let
`t : T ⟶ G` and `u : U ⟶ G` be normal closed subgroups. Suppose that `T` is of multiplicative
type with a unipotent fppf quotient `p : G ⟶ P` by `T`, and that `U` is unipotent with an fppf
quotient `q : G ⟶ Q` by `U` of multiplicative type. Then the points of `T` and `U` commute, and
the multiplication morphism `(x, y) ↦ t(x) · u(y)` from `T × U` to `G` is an isomorphism. -/
def NormalMultiplicativeUnipotentProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (T U P Q : GroupScheme (Spec (CommRingCat.of k)))
    (t : T ⟶ G) (u : U ⟶ G) (p : G ⟶ P) (q : G ⟶ Q),
    IsClosedSubgroup t → (SubgroupFunctor.range t).IsNormal → IsMultiplicativeType T →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range t) p → IsUnipotent P →
    IsClosedSubgroup u → (SubgroupFunctor.range u).IsNormal → IsUnipotent U →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range u) q → IsMultiplicativeType Q →
      (∀ (V : Over (Spec (CommRingCat.of k))) (x : V ⟶ T.X) (y : V ⟶ U.X),
        (x ≫ t.hom.hom) * (y ≫ u.hom.hom) = (y ≫ u.hom.hom) * (x ≫ t.hom.hom)) ∧
      IsIso (subgroupMultiplication t u)

end Langlands.GroupScheme

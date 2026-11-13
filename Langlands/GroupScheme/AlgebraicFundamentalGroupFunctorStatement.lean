import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctor
import Mathlib.FieldTheory.IsSepClosed

/-! # KP Lemma 11.3.6: functoriality of algebraic fundamental groups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

/-- Every reductive morphism has a unique induced map, equivariant and compatible
with every change of the two quotient presentations. -/
def AlgebraicFundamentalGroupMapStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    (_ : IsConnectedReductive H) (_ : IsConnectedReductive G)
    (a : Choice k H) (c : Choice k G) (f : H ⟶ G),
    (∃! m, a.IsInducedMap E c f m) ∧
    a.IsInducedMap E c f (a.mapTo E c f) ∧
    (∀ (σ : E ≃ₐ[k] E) (x : a.atChoice E),
      a.mapTo E c f (a.galoisRepresentation E σ x) =
        c.galoisRepresentation E σ (a.mapTo E c f x)) ∧
    (∀ (a' : Choice k H) (c' : Choice k G),
      (c.comparison E c').comp (a.mapTo E c f) =
        (a'.mapTo E c' f).comp (a.comparison E a'))

/-- The induced maps preserve identities and composition, for every choice
of quotient presentations. -/
def AlgebraicFundamentalGroupFunctorStatement : Prop :=
  ∀ (k E : Type u) [Field k] [Field E] [Algebra k E] [IsSepClosure k E],
    (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (_ : IsConnectedReductive H)
      (a b : Choice k H), a.mapTo E b (𝟙 H) = a.comparison E b) ∧
    (∀ (H G J : GroupScheme (Spec (CommRingCat.of k)))
      (_ : IsConnectedReductive H) (_ : IsConnectedReductive G)
      (_ : IsConnectedReductive J)
      (a : Choice k H) (b : Choice k G) (c : Choice k J)
      (f : H ⟶ G) (g : G ⟶ J),
      (b.mapTo E c g).comp (a.mapTo E b f) = a.mapTo E c (f ≫ g))

end Langlands.GroupScheme.AlgebraicFundamentalGroup

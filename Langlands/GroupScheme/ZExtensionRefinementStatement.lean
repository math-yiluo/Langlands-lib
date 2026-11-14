import Langlands.GroupScheme.ZExtension

/-! # Compatible common refinements of z-extensions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- KP Lemma 11.4.3: any homomorphism of connected reductive field groups
can be lifted after refining a supplied z-extension of its source. -/
def ZExtensionMorphismDominationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G H : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsConnectedReductive H →
    ∀ (z : ZExtension G) (t : ZExtension H) (f : G ⟶ H),
      ∃ (w : ZExtension G) (r : w.H ⟶ z.H) (s : w.H ⟶ t.H),
        r ≫ z.p = w.p ∧ s ≫ t.p = w.p ≫ f

/-- KP Fact 11.4.2, as a consequence of its fiber product: two supplied
z-extensions of the same connected reductive field group have a common
dominating z-extension. -/
def ZExtensionCommonDominationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (z t : ZExtension G),
      ∃ (w : ZExtension G) (r : w.H ⟶ z.H) (s : w.H ⟶ t.H),
        r ≫ z.p = w.p ∧ s ≫ t.p = w.p

end Langlands.GroupScheme

import Langlands.GroupScheme.ZExtension

/-! # Existence of z-extensions over every field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- KP Construction 11.4.1: every connected reductive group over any field
has a z-extension by an induced torus with simply connected derived group. -/
def ZExtensionExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → Nonempty (ZExtension G)

end Langlands.GroupScheme

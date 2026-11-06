import Langlands.GroupScheme.AlgebraicallyClosedComponentBaseChange

/-! # Invariance of actual components under algebraically closed field extension -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityComponent

/-- Extending an algebraically closed field to another algebraically closed
field induces a bijection on the actual components of a smooth affine group
scheme, via the published homomorphism defined by pulled-back sections. -/
def AlgebraicallyClosedComponentBaseChangeStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [IsAlgClosed k] [IsAlgClosed L]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] (φ : k →+* L),
    Function.Bijective (allComponentBaseChange H φ)

end Langlands.GroupScheme.IdentityComponent

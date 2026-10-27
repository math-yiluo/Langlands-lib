import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Preservation of ampleness under base change of the ground field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a scheme `X` over a field `k` and any morphism `Spec K ⟶ Spec k` from the spectrum
of a field `K`, the actual pullback of an ample line bundle along the base-change projection
`X ×_{Spec k} Spec K ⟶ X` is ample. This proposition is a statement target, not a proof. -/
def FieldBaseChangeAmpleStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (L : LineBundle X),
    L.IsAmple →
      ((LineBundle.pullback (CategoryTheory.Limits.pullback.fst p b)).obj L).IsAmple

end Langlands.AlgebraicGeometry.Picard

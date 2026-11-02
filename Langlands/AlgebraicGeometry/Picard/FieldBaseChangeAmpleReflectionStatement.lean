import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Reflection of ampleness of a fixed line bundle along field base change -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a scheme `X` over a field `k`, any morphism `Spec K ⟶ Spec k` from the spectrum of a
field `K`, and a line bundle `L` on `X`, if the actual pullback of `L` along the base-change
projection `X ×_{Spec k} Spec K ⟶ X` is ample, then `L` itself is ample. This proposition is
a statement target, not a proof. -/
def FieldBaseChangeAmpleReflectionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (L : LineBundle X),
    ((LineBundle.pullback (CategoryTheory.Limits.pullback.fst p b)).obj L).IsAmple →
      L.IsAmple

end Langlands.AlgebraicGeometry.Picard

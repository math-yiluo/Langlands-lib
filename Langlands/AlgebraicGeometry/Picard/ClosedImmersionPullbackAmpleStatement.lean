import Langlands.AlgebraicGeometry.Picard.Ample
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Preservation of ampleness by closed-immersion pullback -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- The actual pullback of an ample line bundle along any closed immersion is ample. -/
def ClosedImmersionPullbackAmpleStatement : Prop :=
  ∀ (X Z : Scheme.{u}) (i : Z ⟶ X) (L : LineBundle X),
    IsClosedImmersion i → L.IsAmple → ((LineBundle.pullback i).obj L).IsAmple

end Langlands.AlgebraicGeometry.Picard

import Langlands.AlgebraicGeometry.Picard.Ample

/-!
# Ampleness under positive tensor powers and sheaf isomorphisms

This proposition states the forward direction of Stacks Lemma 28.27.2,
transported to any actual line bundle with the displayed sheaf isomorphism.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- An actual line bundle isomorphic to a positive tensor power of an ample
line bundle is ample. -/
def PositiveTensorPowerAmpleStatement : Prop :=
  ∀ (X : Scheme.{u}) (L M : LineBundle X) (n : ℕ),
    0 < n → L.IsAmple →
      Nonempty (M.obj ≅ Langlands.Scheme.Modules.tensorPow L.obj n) → M.IsAmple

end Langlands.AlgebraicGeometry.Picard

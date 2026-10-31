import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Constant relative dimension of a smooth morphism with connected source -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Every smooth morphism of schemes `f : X ⟶ Y` whose source `X` is connected (in particular
nonempty) is smooth of relative dimension `n` for some natural number `n`, in the sense of
Mathlib's standard-smooth-chart predicate `SmoothOfRelativeDimension`.
This proposition is a statement target, not a proof. -/
def SmoothConnectedRelativeDimensionStatement : Prop :=
  ∀ (X Y : _root_.AlgebraicGeometry.Scheme.{u}) (f : X ⟶ Y),
    Smooth f → ConnectedSpace X → ∃ n : ℕ, SmoothOfRelativeDimension n f

end Langlands.AlgebraicGeometry

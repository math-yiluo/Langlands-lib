import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Geometric reducedness from algebraically closed base changes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A morphism of schemes is geometrically reduced as soon as its base change along every
morphism from the spectrum of an algebraically closed field is reduced. -/
def GeometricallyReducedOfAlgClosedStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    (∀ (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (.of K) ⟶ Y),
      IsReduced (pullback f y)) →
      GeometricallyReduced f

end Langlands.AlgebraicGeometry

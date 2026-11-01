import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness from transitivity on closed points -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

/-- A reduced scheme locally of finite type over an algebraically closed field
is smooth if its automorphisms over the field act transitively on closed points. -/
def ClosedPointHomogeneousSmoothStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [IsReduced X],
    (∀ (x y : X), IsClosed ({x} : Set X) → IsClosed ({y} : Set X) →
      ∃ α : X ≅ X, α.hom ≫ f = f ∧ α.hom x = y) →
    Smooth f

end Langlands.AlgebraicGeometry

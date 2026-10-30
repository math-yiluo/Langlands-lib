import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties

/-! # Stalk dimension at a closed point of a smooth scheme over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- If a scheme `X` is smooth of relative dimension `g` over an arbitrary field `k`, then the
stalk of `X` at every closed point has Krull dimension `g`.
This proposition is a statement target, not a proof. -/
def FieldSmoothClosedPointStalkDimensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ),
    SmoothOfRelativeDimension g f → ∀ (x : X),
      IsClosed ({x} : Set X) →
        ringKrullDim (X.presheaf.stalk x) = (g : WithBot ℕ∞)

end Langlands.AlgebraicGeometry

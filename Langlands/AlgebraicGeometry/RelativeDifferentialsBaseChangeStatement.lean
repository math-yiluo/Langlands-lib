import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChange

/-! # Arbitrary base change for relative differentials -/

universe u

open CategoryTheory

namespace Langlands.Scheme

/-- The canonical relative differential comparison is invertible after arbitrary base change. -/
def RelativeDifferentialsBaseChangeIsIsoStatement (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (X T : AlgebraicGeometry.Scheme.{u}) (f : X ⟶ S) (b : T ⟶ S),
    IsIso (relativeDifferentialsBaseChangeMap f b)

end Langlands.Scheme

import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChange

/-! # Canonical differential base change for spectra -/

universe u

open CategoryTheory

namespace Langlands.Scheme

/-- The canonical relative differential comparison is invertible for base change of spectra. -/
def RelativeDifferentialsAffineBaseChangeIsIsoStatement : Prop :=
  ∀ (R A B : CommRingCat.{u}) (f : R ⟶ A) (b : R ⟶ B),
    IsIso (relativeDifferentialsBaseChangeMap
      (AlgebraicGeometry.Spec.map f) (AlgebraicGeometry.Spec.map b))

end Langlands.Scheme

import Langlands.GroupScheme.GeneralLinearSmoothStatement
import Langlands.GroupScheme.GeneralLinearLocalization

noncomputable section
universe u
open AlgebraicGeometry

namespace Langlands.GroupScheme.GeneralLinear

variable (n : Type) [Fintype n] [DecidableEq n] (R : Type u) [CommRing R]

/-- The explicit two-matrix coordinate ring is a smooth algebra over its base. -/
theorem coordinateRing_smooth : Algebra.Smooth R (CoordinateRing n R) := by
  let : Algebra.Smooth R (MatrixPolynomial n R) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth (MatrixPolynomial n R) (DeterminantLocalization n R) :=
    Algebra.Smooth.of_isLocalization_Away (determinantPolynomial n R)
  let : Algebra.Smooth R (DeterminantLocalization n R) :=
    Algebra.Smooth.comp R (MatrixPolynomial n R) (DeterminantLocalization n R)
  exact Algebra.Smooth.of_equiv (determinantLocalizationEquiv n R).symm

/-- Smoothness of the published general linear group scheme. -/
theorem smoothStatement : SmoothStatement.{u} := by
  intro n _ _ R
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing n R))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap R (CoordinateRing n R)).Smooth
  rw [RingHom.smooth_algebraMap]
  exact coordinateRing_smooth n R

end Langlands.GroupScheme.GeneralLinear

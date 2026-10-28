import Langlands.AlgebraicGeometry.Picard.LocalComparisonDirections
import Langlands.AlgebraicGeometry.Modules.TensorLocalUnitFactorizationProof
import Langlands.CategoryTheory.Picard.UnitTensorCancellationProof

/-!
# Tensor-invertible scheme modules are locally free of rank one

Local unit factorization and categorical cancellation give actual neighborhood
trivializations for the published symmetric monoidal tensor.
-/

universe u

open CategoryTheory MonoidalCategory

namespace Langlands.AlgebraicGeometry.Picard

/-- A tensor-invertible scheme-module sheaf is locally free of rank one. -/
theorem tensorInvertibleLocallyFreeRankOne
    (X : _root_.AlgebraicGeometry.Scheme.{u}) :
    TensorInvertibleLocallyFreeRankOneStatement X := by
  intro M hM x
  obtain ⟨N, ⟨e⟩⟩ := hM
  obtain ⟨U, hx, s, t, hst⟩ :=
    Langlands.Scheme.Modules.tensorLocalUnitFactorization X M N e x
  let : IsIso s :=
    (Langlands.CategoryTheory.Picard.unitTensorCancellation U.toScheme.Modules _ _ s t hst).1
  exact ⟨U, hx, ⟨(asIso s).symm⟩⟩

end Langlands.AlgebraicGeometry.Picard

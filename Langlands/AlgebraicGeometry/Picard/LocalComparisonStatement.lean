import Langlands.AlgebraicGeometry.Modules.TensorMonoidal
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.CategoryTheory.Picard.Basic

/-!
# Tensor-invertibility and local rank one on schemes

The comparison uses the published symmetric monoidal structure on actual
scheme-module sheaves. This file states the comparison as a proposition.
-/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- For the actual sheaf tensor on a scheme, tensor-invertibility is equivalent
to local freeness of rank one. This definition states the comparison. -/
def LocallyFreeRankOneIffTensorInvertibleStatement
    (X : _root_.AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ M : X.Modules,
    Langlands.CategoryTheory.TensorInvertible M ↔ IsLocallyFreeRankOne M

end Langlands.AlgebraicGeometry.Picard

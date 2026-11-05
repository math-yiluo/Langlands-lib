import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Localization.BaseChange

noncomputable section

universe u v w z

open scoped TensorProduct

namespace Langlands.Global

variable (R : Type u) (V : Type v) (B : Type w) (L : Type z)
  [CommRing R] [CommRing V] [CommRing B] [CommRing L]
  [Algebra R V] [Algebra R B] [Algebra R L] [Algebra V L]
  [IsScalarTower R V L] [Algebra B L] [IsScalarTower R B L]
  [IsIntegralClosure B R L] (M : Submonoid R) [IsLocalization M V]

/-- Original integral closure commutes with the actual lower localization, with its coefficient maps. -/
def integralClosureLocalizationTensorEquiv : V ⊗[R] B ≃ₐ[V] integralClosure V L :=
  ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := V) (A₁ := V))
      (IsIntegralClosure.equiv R B L (integralClosure R L))).trans
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R V L)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization M))).trans
    (AlgEquiv.mapIntegralClosure (IsLocalization.algebraLid M V L))

/-- Pure tensors map to the product of the two original coefficient images. -/
@[simp]
theorem integralClosureLocalizationTensorEquiv_tmul (a : V) (b : B) :
    (integralClosureLocalizationTensorEquiv R V B L M (a ⊗ₜ[R] b) : L) =
      algebraMap V L a * algebraMap B L b := by
  simp [integralClosureLocalizationTensorEquiv, TensorProduct.toIntegralClosure,
    IsLocalization.algebraLid, Algebra.TensorProduct.lidOfCompatibleSMul_tmul,
    Algebra.smul_def]
  exact congrArg (fun y : L => algebraMap V L a * y)
    (IsIntegralClosure.algebraMap_equiv R B L (integralClosure R L) b)

/-- The upper original integral-closure inclusion is unchanged on the right tensor factor. -/
@[simp]
theorem integralClosureLocalizationTensorEquiv_one_tmul (b : B) :
    (integralClosureLocalizationTensorEquiv R V B L M (1 ⊗ₜ[R] b) : L) =
      algebraMap B L b := by
  simp only [integralClosureLocalizationTensorEquiv_tmul, map_one, one_mul]

end Langlands.Global

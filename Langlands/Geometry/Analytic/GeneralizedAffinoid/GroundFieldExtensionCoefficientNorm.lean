import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionCoefficientAction

/-! # Quotient norms for the scalar-extension coefficient action -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open CompletedTensorAlgebra GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (A : PresentedAffinoidAlgebra K)

local notation "B" => algebra K L A
local notation "T" => CompletedTensorAlgebra.Algebra K A L

omit [CompleteSpace L] in
private theorem norm_toTensor_le (b : B) : ‖toTensor K L A b‖ ≤ ‖b‖ := by
  let := (algebra K L A).ideal_closed
  have h := BoundedAlgHom.quotient_norm_bound (algebra K L A).ideal (toTensorRingHom K L A) 1
    zero_lt_one (fun f => by
      change ‖tensorEvaluation K L A f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact norm_evaluateCoefficients_le A.polyradius (rightMap K A L) (tensorTuple K L A)
        (norm_rightMap_le_self K L A) (tensorTuple_monomial_le K L A) f) b
  change ‖toTensorRingHom K L A b‖ ≤ ‖b‖
  rw [one_mul] at h
  exact h

omit [CompleteSpace L] in
private theorem norm_scalarMap_le (c : L) : ‖scalarMap K L A c‖ ≤ ‖c‖ := by
  change ‖algebraMap L B c‖ ≤ ‖c‖
  calc
    ‖algebraMap L B c‖ = ‖c • (1 : B)‖ := by rw [_root_.Algebra.smul_def, mul_one]
    _ ≤ ‖c‖ * ‖(1 : B)‖ := norm_smul_le _ _
    _ ≤ ‖c‖ := mul_le_of_le_one_right (norm_nonneg c) (norm_one_le L B)

private def coefficientLeg (σ : isometricAutomorphisms K L) : BoundedAlgHom K L B where
  toAlgHom := (scalarMap K L A).toAlgHom.comp σ.val.toAlgHom
  bounded := ⟨1, zero_lt_one, fun c => by
    change ‖scalarMap K L A (σ.val c)‖ ≤ 1 * ‖c‖
    rw [one_mul, ← σ.property c]
    exact norm_scalarMap_le K L A (σ.val c)⟩

private theorem coefficientHom_comp_fromTensor (σ : isometricAutomorphisms K L) :
    (coefficientHom K L A σ).comp (fromTensor K L A) =
      CompletedTensorAlgebra.lift (iota K L A) (coefficientLeg K L A σ) := by
  apply CompletedTensorAlgebra.hom_ext
  · rw [lift_comp_leftMap]
    apply BoundedAlgHom.ext
    intro a
    simp only [BoundedAlgHom.comp_apply, fromTensor_leftMap, coefficientHom_iota]
  · rw [lift_comp_rightMap]
    apply BoundedAlgHom.ext
    intro c
    simp only [BoundedAlgHom.comp_apply, fromTensor_rightMap, coefficientHom_scalar]
    rfl

/-- The actual coefficient automorphism is contractive for the quotient norm
of the scalar-extended affinoid presentation. -/
theorem norm_coefficientHom_le (σ : isometricAutomorphisms K L) (b : B) :
    ‖coefficientHom K L A σ b‖ ≤ ‖b‖ := by
  have h := congrArg (fun f : BoundedAlgHom K T B => f (toTensor K L A b))
    (coefficientHom_comp_fromTensor K L A σ)
  change coefficientHom K L A σ (fromTensor K L A (toTensor K L A b)) =
    extensionRingHom (iota K L A) (coefficientLeg K L A σ) (toTensor K L A b) at h
  rw [fromTensor_toTensor] at h
  rw [h]
  refine (norm_extensionRingHom_le (iota K L A) (coefficientLeg K L A σ)
    1 1 zero_lt_one zero_lt_one (fun a => by simpa only [one_mul] using norm_iota_le K L A a)
    (fun c => ?_) _).trans ?_
  · change ‖scalarMap K L A (σ.val c)‖ ≤ 1 * ‖c‖
    rw [one_mul, ← σ.property c]
    exact norm_scalarMap_le K L A (σ.val c)
  · simpa only [one_mul] using norm_toTensor_le K L A b

/-- Applying the same contraction to the inverse gives exact norm preservation. -/
theorem norm_coefficientHom (σ : isometricAutomorphisms K L) (b : B) :
    ‖coefficientHom K L A σ b‖ = ‖b‖ := by
  refine le_antisymm (norm_coefficientHom_le K L A σ b) ?_
  have h := norm_coefficientHom_le K L A σ⁻¹ (coefficientHom K L A σ b)
  rwa [← BoundedAlgHom.comp_apply, ← coefficientHom_mul, inv_mul_cancel,
    coefficientHom_one, BoundedAlgHom.id_apply] at h

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

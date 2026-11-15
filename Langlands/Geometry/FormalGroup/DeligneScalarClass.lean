import Langlands.Geometry.FormalGroup.DeligneScalarPeriod

/-! # Triviality of the normalized scalar action on actual Deligne classes -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry

variable {F : Type u} [Field F] {d : ℕ}

/-- The determinant of the actual scalar linear automorphism is its d-th power. -/
@[simp]
theorem det_scalarReframeHom (a : Fˣ) :
    LinearEquiv.det (scalarReframeHom d F a) = a ^ d := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have hm : (scalarReframeHom d F a).toLinearMap =
      (a : F) • (LinearMap.id : (Fin d → F) →ₗ[F] (Fin d → F)) := by
    apply LinearMap.ext
    intro v
    rfl
  rw [hm]
  simp

variable {O : Type u} [CommRing O] [Algebra O F] {π : O}

section Preliminary

variable [NeZero d] {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum.IsoClass

/-- The constructed integral-unit isomorphism identifies genuine preliminary classes. -/
@[simp]
theorem reframe_integralUnit (a : Oˣ)
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    reframe (scalarReframeHom d F (Units.map (algebraMap O F).toMonoidHom a)) q = q := by
  induction q using Quotient.inductionOn with
  | h D => exact Quotient.sound ⟨D.reframeIntegralUnitIso a⟩

/-- The actual uniformizer period identifies genuine preliminary classes. -/
@[simp]
theorem shiftReframe_uniformizerInverse (hπ : algebraMap O F π ≠ 0)
    (q : IsoClass (d := d) (π := π) (F := F) (φ := φ)) :
    shiftReframe hπ (scalarReframeHom d F (Units.mk0 (algebraMap O F π) hπ)⁻¹)
      (d : ℤ) q = q := by
  induction q using Quotient.inductionOn with
  | h D => exact Quotient.sound ⟨D.uniformizerInverseReframeIso hπ⟩

end SheafPreDatum.IsoClass

end Preliminary

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- The correcting shift of a scalar is minus d times its normalized coefficient order. -/
@[simp]
theorem coefficientOrder_det_scalarReframeHom (a : Fˣ) :
    (coefficientOrder O F (LinearEquiv.det (scalarReframeHom d F a))).toAdd =
      (d : ℤ) * (coefficientOrder O F a).toAdd := by
  rw [det_scalarReframeHom, map_pow]
  simp

variable [NeZero d] {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafDatum.IsoClass

variable (hπ : Irreducible π)

/-- Integral units act trivially under the actual valuation-normalized action. -/
@[simp]
theorem normalizedReframe_integralUnit (a : Oˣ)
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    normalizedReframe hπ
      (scalarReframeHom d F (Units.map (algebraMap O F).toMonoidHom a)) q = q := by
  apply toPreliminary_injective (coefficientUniformizer_ne_zero (F := F) hπ)
  rw [toPreliminary_normalizedReframe]
  simp only [coefficientOrder_det_scalarReframeHom, coefficientOrder_algebraMap_unit,
    toAdd_one, mul_zero, neg_zero, SheafPreDatum.IsoClass.shiftReframe,
    SheafPreDatum.IsoClass.shiftInt_zero, SheafPreDatum.IsoClass.reframe_integralUnit]

/-- Inverse uniformizer scalars have correcting shift d and act trivially. -/
@[simp]
theorem normalizedReframe_uniformizerInverse
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    normalizedReframe hπ
      (scalarReframeHom d F
        (Units.mk0 (algebraMap O F π) (coefficientUniformizer_ne_zero (F := F) hπ))⁻¹) q = q := by
  apply toPreliminary_injective (coefficientUniformizer_ne_zero (F := F) hπ)
  rw [toPreliminary_normalizedReframe]
  have hs :
      -(coefficientOrder O F (LinearEquiv.det
        (scalarReframeHom d F
          (Units.mk0 (algebraMap O F π) (coefficientUniformizer_ne_zero (F := F) hπ))⁻¹))).toAdd =
        (d : ℤ) := by
    rw [coefficientOrder_det_scalarReframeHom, map_inv,
      coefficientOrder_uniformizer hπ]
    simp
  rw [hs]
  exact SheafPreDatum.IsoClass.shiftReframe_uniformizerInverse _ _

/-- The subgroup of field scalars fixing every actual admissible isomorphism class. -/
def normalizedScalarKernel : Subgroup Fˣ where
  carrier a := ∀ q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ),
    normalizedReframe hπ (scalarReframeHom d F a) q = q
  one_mem' q := by rw [map_one, normalizedReframe_one]
  mul_mem' {a b} ha hb q := by
    rw [map_mul, ← normalizedReframe_mul, hb, ha]
  inv_mem' {a} ha q := by
    rw [map_inv]
    have h := normalizedReframe_inv_normalizedReframe hπ (scalarReframeHom d F a) q
    rw [ha q] at h
    exact h

/-- Every field scalar fixes the genuine admissible classes under the normalized action. -/
@[simp]
theorem normalizedReframe_scalar (a : Fˣ)
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    normalizedReframe hπ (scalarReframeHom d F a) q = q := by
  let K := normalizedScalarKernel (F := F) (d := d) (φ := φ) hπ
  let p := Units.mk0 (algebraMap O F π) (coefficientUniformizer_ne_zero (F := F) hπ)
  have hi : p⁻¹ ∈ K := normalizedReframe_uniformizerInverse hπ
  have hp : p ∈ K := by simpa only [inv_inv] using K.inv_mem hi
  obtain ⟨b, hb⟩ := exists_coefficientOrder_correction hπ a
  have hb' : p ^ (-(coefficientOrder O F a).toAdd) * a =
      Units.map (algebraMap O F).toMonoidHom b := by
    apply Units.ext
    simpa [p] using hb
  have ha : a = p ^ (coefficientOrder O F a).toAdd *
      Units.map (algebraMap O F).toMonoidHom b := by
    rw [← hb', ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have hu : Units.map (algebraMap O F).toMonoidHom b ∈ K :=
    normalizedReframe_integralUnit hπ b
  have hmem : a ∈ K := by
    rw [ha]
    exact K.mul_mem (K.zpow_mem hp _) hu
  exact hmem q

/-- The actual scalar kernel is the whole multiplicative group of the coefficient field. -/
theorem normalizedScalarKernel_eq_top :
    normalizedScalarKernel (F := F) (d := d) (φ := φ) hπ = ⊤ := by
  apply top_unique
  intro a _
  exact normalizedReframe_scalar hπ a

end SheafDatum.IsoClass

end Langlands.DeligneFormalSpace

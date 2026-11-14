import Langlands.Geometry.FormalGroup.DeligneShiftReframe
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! # The DVR-normalized general linear action on actual Deligne classes -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry
open scoped WithZero

variable (O F : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field F] [Algebra O F] [IsFractionRing O F]

/-- The actual adic valuation at the maximal ideal of the coefficient DVR. -/
def coefficientValuation : Valuation F ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal O).valuation F

/-- The normalized additive order on nonzero field elements, as a group homomorphism. -/
def coefficientOrder : Fˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (-WithZero.log (coefficientValuation O F (a : F)))
  map_one' := by simp [coefficientValuation]
  map_mul' a b := by
    change Multiplicative.ofAdd
        (-WithZero.log (coefficientValuation O F ((a : F) * (b : F)))) = _
    rw [map_mul, WithZero.log_mul
      ((coefficientValuation O F).ne_zero_iff.mpr a.ne_zero)
      ((coefficientValuation O F).ne_zero_iff.mpr b.ne_zero)]
    exact congrArg Multiplicative.ofAdd (neg_add _ _)

theorem coefficientValuation_algebraMap_unit (a : Oˣ) :
    coefficientValuation O F (algebraMap O F (a : O)) = 1 := by
  rw [coefficientValuation,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  apply IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
  change (a : O) ∉ IsLocalRing.maximalIdeal O
  simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using a.isUnit

@[simp]
theorem coefficientOrder_algebraMap_unit (a : Oˣ) :
    coefficientOrder O F (Units.map (algebraMap O F).toMonoidHom a) = 1 := by
  change Multiplicative.ofAdd
    (-WithZero.log (coefficientValuation O F (algebraMap O F (a : O)))) = 1
  rw [coefficientValuation_algebraMap_unit]
  rfl

variable {O F} {π : O}

/-- A uniformizer stays nonzero in the actual fraction field. -/
theorem coefficientUniformizer_ne_zero (hπ : Irreducible π) :
    algebraMap O F π ≠ 0 :=
  fun h => hπ.ne_zero (IsFractionRing.injective O F (by simpa using h))

theorem coefficientValuation_uniformizer (hπ : Irreducible π) :
    coefficientValuation O F (algebraMap O F π) = WithZero.exp (-1 : ℤ) := by
  rw [coefficientValuation,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero
    (by change IsLocalRing.maximalIdeal O = Ideal.span {π}; exact hπ.maximalIdeal_eq)

@[simp]
theorem coefficientOrder_uniformizer (hπ : Irreducible π) :
    coefficientOrder O F (Units.mk0 (algebraMap O F π)
      (coefficientUniformizer_ne_zero (F := F) hπ)) = Multiplicative.ofAdd (1 : ℤ) := by
  change Multiplicative.ofAdd
    (-WithZero.log (coefficientValuation O F (algebraMap O F π))) = _
  rw [coefficientValuation_uniformizer hπ]
  simp

/-- DVR fraction-field decomposition gives the precise normalized unit correction. -/
theorem exists_coefficientOrder_correction (hπ : Irreducible π) (a : Fˣ) :
    ∃ b : Oˣ,
      algebraMap O F π ^ (-(coefficientOrder O F a).toAdd) * (a : F) =
        algebraMap O F (b : O) := by
  obtain ⟨n, b, hb⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ a.ne_zero
  rw [Units.smul_def, Algebra.smul_def] at hb
  have hb' : a = Units.map (algebraMap O F).toMonoidHom b *
      Units.mk0 (algebraMap O F π) (coefficientUniformizer_ne_zero (F := F) hπ) ^ n := by
    apply Units.ext
    simpa using hb
  have hn : (coefficientOrder O F a).toAdd = n := by
    rw [hb', map_mul, coefficientOrder_algebraMap_unit, one_mul, map_zpow,
      coefficientOrder_uniformizer hπ]
    simp
  refine ⟨b, ?_⟩
  rw [hn, hb]
  calc
    algebraMap O F π ^ (-n) *
        (algebraMap O F (b : O) * algebraMap O F π ^ n) =
      algebraMap O F (b : O) *
        (algebraMap O F π ^ (-n) * algebraMap O F π ^ n) := by ac_rfl
    _ = algebraMap O F (b : O) := by
      rw [← zpow_add₀ (coefficientUniformizer_ne_zero (F := F) hπ), neg_add_cancel,
        zpow_zero, mul_one]

variable {d : ℕ}

/-- Every linear automorphism has a canonical determinant-corrected pair. -/
def normalizedReframeHom (hπ : Irreducible π) :
    ((Fin d → F) ≃ₗ[F] (Fin d → F)) →*
      shiftReframeSubgroup (d := d) (coefficientUniformizer_ne_zero (F := F) hπ) where
  toFun g := ⟨(g, (coefficientOrder O F (LinearEquiv.det g))⁻¹), by
    apply (mem_shiftReframeSubgroup_iff
      (coefficientUniformizer_ne_zero (F := F) hπ) _).mpr
    simpa using exists_coefficientOrder_correction hπ (LinearEquiv.det g)⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp
  map_mul' g h := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · simp [mul_comm]

@[simp]
theorem normalizedReframeHom_linear (hπ : Irreducible π)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    (normalizedReframeHom hπ g).val.1 = g := rfl

/-- The correcting shift is exactly minus the normalized determinant order. -/
@[simp]
theorem normalizedReframeHom_shift (hπ : Irreducible π)
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    (normalizedReframeHom hπ g).val.2.toAdd =
      -(coefficientOrder O F (LinearEquiv.det g)).toAdd := rfl

variable [NeZero d] {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

/-- The canonical valuation correction preserves all three actual conditions. -/
theorem admissible_normalizedReframe_iff (D : SheafPreDatum d π F φ)
    (hπ : Irreducible π) (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    (D.shiftReframe (coefficientUniformizer_ne_zero (F := F) hπ) g
      (-(coefficientOrder O F (LinearEquiv.det g)).toAdd)).Admissible
        (coefficientUniformizer_ne_zero (F := F) hπ) ↔
      D.Admissible (coefficientUniformizer_ne_zero (F := F) hπ) :=
  D.admissible_shiftReframe_iff (coefficientUniformizer_ne_zero (F := F) hπ)
    (normalizedReframeHom hπ g)

end SheafPreDatum

namespace SheafDatum

variable (hπ : Irreducible π)

/-- Apply the actual integer shift and frame change with the derived correction. -/
def normalizedReframe (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (D : SheafDatum (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    SheafDatum (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ) :=
  shiftReframe (coefficientUniformizer_ne_zero (F := F) hπ) (normalizedReframeHom hπ g) D

@[simp]
theorem normalizedReframe_val (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (D : SheafDatum (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    (normalizedReframe hπ g D).val =
      D.val.shiftReframe (coefficientUniformizer_ne_zero (F := F) hπ) g
        (-(coefficientOrder O F (LinearEquiv.det g)).toAdd) := rfl

namespace IsoClass

/-- The full general linear group acts on the existing genuine admissible classes. -/
def normalizedReframe (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    IsoClass (d := d) (π := π) (φ := φ) (coefficientUniformizer_ne_zero (F := F) hπ) →
      IsoClass (d := d) (π := π) (φ := φ) (coefficientUniformizer_ne_zero (F := F) hπ) :=
  shiftReframe (coefficientUniformizer_ne_zero (F := F) hπ) (normalizedReframeHom hπ g)

@[simp]
theorem normalizedReframe_mk (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (D : SheafDatum (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    normalizedReframe hπ g (mk _ D) =
      mk _ (SheafDatum.normalizedReframe hπ g D) := rfl

@[simp]
theorem toPreliminary_normalizedReframe (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    toPreliminary _ (normalizedReframe hπ g q) =
      SheafPreDatum.IsoClass.shiftReframe (coefficientUniformizer_ne_zero (F := F) hπ) g
        (-(coefficientOrder O F (LinearEquiv.det g)).toAdd) (toPreliminary _ q) :=
  toPreliminary_shiftReframe _ _ _

@[simp]
theorem normalizedReframe_one
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    normalizedReframe hπ 1 q = q := by
  unfold normalizedReframe
  rw [map_one, shiftReframe_one]

/-- Successive corrected frame changes satisfy the right general linear action law. -/
theorem normalizedReframe_mul (g h : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    normalizedReframe hπ h (normalizedReframe hπ g q) =
      normalizedReframe hπ (g * h) q := by
  unfold normalizedReframe
  rw [shiftReframe_mul, map_mul]

@[simp]
theorem normalizedReframe_inv_normalizedReframe
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    normalizedReframe hπ g⁻¹ (normalizedReframe hπ g q) = q := by
  rw [normalizedReframe_mul, mul_inv_cancel, normalizedReframe_one]

@[simp]
theorem normalizedReframe_normalizedReframe_inv
    (g : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (q : IsoClass (d := d) (π := π) (φ := φ)
      (coefficientUniformizer_ne_zero (F := F) hπ)) :
    normalizedReframe hπ g (normalizedReframe hπ g⁻¹ q) = q := by
  rw [normalizedReframe_mul, inv_mul_cancel, normalizedReframe_one]

/-- Every corrected general linear operation is an actual bijection of classes. -/
def normalizedReframeEquiv (g : (Fin d → F) ≃ₗ[F] (Fin d → F)) :
    IsoClass (d := d) (π := π) (φ := φ) (coefficientUniformizer_ne_zero (F := F) hπ) ≃
      IsoClass (d := d) (π := π) (φ := φ) (coefficientUniformizer_ne_zero (F := F) hπ) where
  toFun := normalizedReframe hπ g
  invFun := normalizedReframe hπ g⁻¹
  left_inv := normalizedReframe_inv_normalizedReframe hπ g
  right_inv := normalizedReframe_normalizedReframe_inv hπ g

/-- Encode the constructed right GL action by a left action of the opposite group. -/
instance normalizedReframeRightAction :
    MulAction (((Fin d → F) ≃ₗ[F] (Fin d → F))ᵐᵒᵖ)
      (IsoClass (d := d) (π := π) (φ := φ) (coefficientUniformizer_ne_zero (F := F) hπ)) where
  smul g q := normalizedReframe hπ g.unop q
  one_smul := normalizedReframe_one hπ
  mul_smul g h q := (normalizedReframe_mul hπ h.unop g.unop q).symm

end IsoClass

end SheafDatum

end Langlands.DeligneFormalSpace

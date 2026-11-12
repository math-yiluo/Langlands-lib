import Langlands.Representation.Hecke.CompactInductionModels
import Langlands.Representation.Jacquet.PositiveCharacter

/-! # The smooth positive square root of the relative modular character -/

noncomputable section

open MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Induction

universe uG

/-- The positive square root of an open-kernel positive character, as a smooth
complex character. -/
def positiveHalfSmoothCharacter {H : Type*} [Group H] [TopologicalSpace H]
    (δ : H →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set H)) : SmoothCharacter ℂ H where
  toMonoidHom := Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ)
  isOpen_ker := by
    have he : (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ)).ker = δ.ker := by
      ext h
      change _ = 1 ↔ _ = 1
      rw [Units.ext_iff, Units.ext_iff]
      simp
    simpa only [he] using hδ

/-- The square root has strictly positive real values and squares to the original
complex character. -/
theorem positiveHalfSmoothCharacter_spec {H : Type*} [Group H] [TopologicalSpace H]
    (δ : H →* ℝ≥0ˣ) (hδ : IsOpen (δ.ker : Set H)) :
    (∀ h : H, ∃ r : ℝ, 0 < r ∧
      ((positiveHalfSmoothCharacter δ hδ).toMonoidHom h : ℂ) = r) ∧
    ∀ h : H, ((positiveHalfSmoothCharacter δ hδ).toMonoidHom h : ℂ) ^ 2 =
      (Jacquet.complexCharacter δ h : ℂ) := by
  constructor
  · intro h
    refine ⟨(NNReal.sqrt (δ h : ℝ≥0) : ℝ), ?_, rfl⟩
    exact NNReal.coe_pos.mpr
      (NNReal.sqrt_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero (δ h))))
  · intro h
    change (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ) h : ℂ) ^ 2 = _
    simp only [Jacquet.complexCharacter_apply, Jacquet.positiveHalfCharacter_apply]
    norm_cast
    exact NNReal.sq_sqrt _

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G]

/-- The relative modular character, before embedding positive reals into the
complex numbers. -/
def relativePositiveModulus (H : Subgroup G) [LocallyCompactSpace H] : H →* ℝ≥0ˣ :=
  (modularCharacter (G := H)).toHomUnits *
    ((modularCharacter (G := G)).toHomUnits.comp H.subtype)⁻¹

/-- Its complex character is exactly the published relative modular character. -/
theorem complexCharacter_relativePositiveModulus (H : Subgroup G) [LocallyCompactSpace H] :
    Jacquet.complexCharacter (relativePositiveModulus H) =
      (Hecke.Homomorphism.relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom := by
  ext h
  change (Jacquet.complexCharacter (relativePositiveModulus H) h : ℂ) =
    Hecke.haarScale h * Hecke.haarScale ((h : G)⁻¹)
  simp [relativePositiveModulus, Hecke.haarScale]

/-- The positive relative modular character has open kernel. -/
theorem isOpen_ker_relativePositiveModulus (H : Subgroup G) [LocallyCompactSpace H] :
    IsOpen ((relativePositiveModulus H).ker : Set H) := by
  have he : (relativePositiveModulus H).ker =
      (Hecke.Homomorphism.relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom.ker := by
    rw [← complexCharacter_relativePositiveModulus]
    ext h
    change _ = 1 ↔ _ = 1
    rw [Units.ext_iff, Units.ext_iff]
    simp
  rw [he]
  exact (Hecke.Homomorphism.relativeModularCharacter H.subtype continuous_subtype_val).isOpen_ker

/-- Existence of the positive smooth half modulus used in Renard IV.2.1. -/
theorem exists_relativeHalfModulus (H : Subgroup G) [LocallyCompactSpace H] :
    ∃ χ : SmoothCharacter ℂ H,
      (∀ h : H, ∃ r : ℝ, 0 < r ∧ (χ.toMonoidHom h : ℂ) = r) ∧
      ∀ h : H, (χ.toMonoidHom h : ℂ) ^ 2 =
        ((Hecke.Homomorphism.relativeModularCharacter H.subtype
          continuous_subtype_val).toMonoidHom h : ℂ) := by
  refine ⟨positiveHalfSmoothCharacter (relativePositiveModulus H)
    (isOpen_ker_relativePositiveModulus H), ?_⟩
  simpa only [complexCharacter_relativePositiveModulus] using
    positiveHalfSmoothCharacter_spec (relativePositiveModulus H)
      (isOpen_ker_relativePositiveModulus H)

end Langlands.Induction

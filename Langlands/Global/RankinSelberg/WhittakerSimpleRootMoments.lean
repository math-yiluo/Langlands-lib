import Langlands.Global.RankinSelberg.WhittakerDetPowerBounds
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerHeights
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices

/-! # Normalized simple-root directions for Whittaker derivatives -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.GroupScheme.GeneralLinear

local instance simpleRootMomentsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

section Algebra

variable {A : Type*} [CommRing A] {r : ℕ} (i : Fin r)

/-- Conjugation by a diagonal cancels the adjacent diagonal ratio in a
simple-root column direction. -/
theorem diagonal_conj_simpleRootColumn (d : Fin (r + 1) → Aˣ) (z : A) :
    (((diagonalMatrixUnits A d)⁻¹ : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) *
        colMatrix (i : ℕ) (Pi.single i.castSucc
          ((d i.castSucc : A) * ((d i.succ)⁻¹ : Aˣ) * z)) *
        (diagonalMatrixUnits A d : Matrix (Fin (r + 1)) (Fin (r + 1)) A) =
      colMatrix (i : ℕ) (Pi.single i.castSucc z) := by
  rw [← map_inv, diagonalMatrixUnits_val, diagonalMatrixUnits_val]
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.inv_apply, colMatrix_apply]
  by_cases ha : a = i.castSucc
  · subst a
    by_cases hb : b = i.succ
    · subst b
      simp only [Fin.val_castSucc, Fin.val_succ, lt_add_iff_pos_right, zero_lt_one,
        and_self, ite_true, Pi.single_eq_same]
      simp [mul_left_comm, mul_comm]
    · have hb' : ¬(b : ℕ) = (i : ℕ) + 1 := fun h => hb (Fin.ext h)
      simp [hb']
  · simp [Pi.single_eq_of_ne ha]

end Algebra

variable (F : Type u) [Field F] [NumberField F]

/-- The conjugated normalized simple-root direction depends only on the
right factor, rather than on the preceding diagonal. -/
theorem colConj_diagonal_mul_simpleRoot {r : ℕ} (i : Fin r)
    (a k : Points F (r + 1)) (d : Fin (r + 1) → (mixedEmbedding.mixedSpace F)ˣ)
    (ha : archCoord F a = diagonalMatrixUnits (mixedEmbedding.mixedSpace F) d)
    (z : mixedEmbedding.mixedSpace F) :
    colConj F (i : ℕ) (a * k)
        (Pi.single i.castSucc
          ((d i.castSucc : mixedEmbedding.mixedSpace F) *
            ((d i.succ)⁻¹ : (mixedEmbedding.mixedSpace F)ˣ) * z)) =
      colConj F (i : ℕ) k (Pi.single i.castSucc z) := by
  simp only [colConj, archCoord_mul, ha, mul_inv_rev, Units.val_mul]
  calc
    _ = (((archCoord F k)⁻¹ : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) *
        ((((diagonalMatrixUnits (mixedEmbedding.mixedSpace F) d)⁻¹ :
          ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) *
          colMatrix (i : ℕ) (Pi.single i.castSucc
            ((d i.castSucc : mixedEmbedding.mixedSpace F) *
              ((d i.succ)⁻¹ : (mixedEmbedding.mixedSpace F)ˣ) * z)) *
          (diagonalMatrixUnits (mixedEmbedding.mixedSpace F) d : ArchimedeanMatrix F (r + 1))) *
        (archCoord F k : ArchimedeanMatrix F (r + 1)) := by simp only [mul_assoc]
    _ = _ := by rw [diagonal_conj_simpleRootColumn]

/-- The padded last row of the identity extracts the designated column entry. -/
theorem colFrequency_padRow_one_single {r : ℕ} (i : Fin r) (b : F)
    (z : mixedEmbedding.mixedSpace F) :
    colFrequency F b (padRow F (r := r) (1 : RationalGL F ((i : ℕ) + 1)))
        (Pi.single i.castSucc z) =
      Langlands.Automorphic.CuspidalWhittaker.mixedTrace F (mixedEmbedding F b * z) := by
  rw [colFrequency, Finset.sum_eq_single i.castSucc]
  · simp [padRow, Matrix.one_apply, Fin.ext_iff]
  · intro a _ ha
    rw [Pi.single_eq_of_ne ha, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

section Moments

open Langlands.Automorphic.CuspidalWhittaker

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
    {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}

/-- Every character-frequency moment of a simple root has the same determinant
power bound, uniformly over diagonals and compact right factors. -/
theorem exists_simpleRoot_frequency_moment_bound
    (hV : WhittakerDecayClass F r V R) (β : ℝ)
    (hβ : ∀ f : V, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
      ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β)
    (N : ℕ) (f : V) {C : Set (Points F (r + 1))} (hC : IsCompact C)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ψ : AddChar (Adeles F) ℂ),
      IsStandardAdditiveCharacter F ψ → ∀ b : F,
      (∀ x, ψ x = EqualAnalytic.standardCharacter F (algebraMap F (Adeles F) b * x)) →
      ∀ (i : Fin r) (a : Points F (r + 1))
        (d : Fin (r + 1) → (mixedEmbedding.mixedSpace F)ˣ),
        archCoord F a = diagonalMatrixUnits (mixedEmbedding.mixedSpace F) d →
      ∀ k ∈ C, ∀ z : mixedEmbedding.mixedSpace F, ‖z‖ ≤ M →
        |mixedTrace F (mixedEmbedding F b *
          ((d i.castSucc : mixedEmbedding.mixedSpace F) *
            ((d i.succ)⁻¹ : (mixedEmbedding.mixedSpace F)ˣ) * z))| ^ N *
          ‖whittaker F r ψ (f : Points F (r + 1) → ℂ) (a * k)‖ ≤
          B * detNorm F (r + 1) (a * k) ^ β := by
  obtain ⟨D, hD, hDC⟩ := exists_archCoord_bound (F := F) hC
  obtain ⟨B₀, hB₀, hB⟩ := exists_norm_whittaker_pow_le_of_detPower F hV β hβ N f
  let A : ℝ := (r + 1 : ℕ) * ((r + 1 : ℕ) * (D * M) * D)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(coordConst F * A) ^ N * B₀,
    mul_nonneg (pow_nonneg (mul_nonneg (coordConst_nonneg F) hA) N) hB₀, ?_⟩
  intro ψ hψ b hb i a d ha k hk z hz
  let w : Fin (r + 1) → mixedEmbedding.mixedSpace F := Pi.single i.castSucc
    ((d i.castSucc : mixedEmbedding.mixedSpace F) *
      ((d i.succ)⁻¹ : (mixedEmbedding.mixedSpace F)ˣ) * z)
  have hw : IsColSupported (i : ℕ) w := by
    intro c hc
    have hne : c ≠ i.castSucc := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc] at this
      omega
    exact Pi.single_eq_of_ne hne _
  have hZ : ∀ c e, ‖colConj F (i : ℕ) k (Pi.single i.castSucc z) c e‖ ≤ A := by
    apply norm_colConj_apply_le (i : ℕ) k (Pi.single i.castSucc z) (hDC k hk)
    intro c
    by_cases hc : c = i.castSucc
    · simpa [hc] using hz
    · simpa [Pi.single_eq_of_ne hc] using hM
  have hderiv := whittaker_pow_deriv_eq F hV ψ hψ hb i.is_lt
    (1 : RationalGL F ((i : ℕ) + 1)) (a * k) hw N f
  have hpad : padRational F (by omega : (i : ℕ) + 1 ≤ r + 1)
      (1 : RationalGL F ((i : ℕ) + 1)) = 1 := by
    simp [padRational]
  dsimp [w] at hderiv
  rw [hpad, one_mul, colConj_diagonal_mul_simpleRoot F i a k d ha z,
    colFrequency_padRow_one_single] at hderiv
  have hbound := hB ψ hψ (colConj F (i : ℕ) k (Pi.single i.castSucc z)) A hZ (a * k)
  rw [hderiv, norm_mul, norm_pow] at hbound
  let L := mixedTrace F (mixedEmbedding F b *
    ((d i.castSucc : mixedEmbedding.mixedSpace F) *
      ((d i.succ)⁻¹ : (mixedEmbedding.mixedSpace F)ˣ) * z))
  have hnorm : ‖(2 * (Real.pi : ℂ) * (L : ℂ) * Complex.I)‖ =
      2 * Real.pi * |L| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_ofNat, mul_one]
  change ‖(2 * (Real.pi : ℂ) * (L : ℂ) * Complex.I)‖ ^ N * _ ≤ _ at hbound
  rw [hnorm] at hbound
  have hL : |L| ^ N ≤ (2 * Real.pi * |L|) ^ N := by
    apply pow_le_pow_left₀ (abs_nonneg L) _ N
    have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [abs_nonneg L]
  exact (mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans hbound

end Moments

end Langlands.Global.RankinSelbergGlobal.Unfolding

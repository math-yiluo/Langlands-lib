import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Representation.Whittaker.Iwasawa

/-! # Changing the generic character of the real uniform coefficient model -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCharacterChange

open Langlands.LocalFactor.Archimedean Langlands.Archimedean
open GeneralLinear.Iwasawa (diagonalUnits_mul_mul_apply)

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ

/-- The diagonal with entries `a^r, a^(r-1), …, 1`. -/
def changeDiagonal (r : ℕ) (a : ℝˣ) : Langlands.GeneralLinear (r + 1) ℝ :=
  GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) (fun i : Fin (r + 1) => a ^ (r - i.val))

/-- Every invertible diagonal matrix normalizes the upper unitriangular subgroup. -/
theorem diagonal_conj_mem (d : Fin (r + 1) → ℝˣ) (u : G) (hu : u ∈ N) :
    GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) d * u *
      (GeneralLinear.Iwasawa.diagonalUnits (F := ℝ) d)⁻¹ ∈ N := by
  rw [← map_inv]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [diagonalUnits_mul_mul_apply, hu.1 hij, mul_zero, zero_mul]
  · rw [diagonalUnits_mul_mul_apply, hu.2 i, mul_one, Pi.inv_apply, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]

/-- Conjugation by the inverse diagonal multiplies each simple-root entry by `a⁻¹`. -/
theorem changeDiagonal_inv_conj_entry (a : ℝˣ) (u : G) (i : Fin r) :
    ((changeDiagonal r a)⁻¹ * u * changeDiagonal r a) i.castSucc i.succ =
      (a⁻¹ : ℝˣ) * u i.castSucc i.succ := by
  have hi : r - i.castSucc.val = r - i.succ.val + 1 := by
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  have hpow : ((a ^ (r - i.castSucc.val))⁻¹ * a ^ (r - i.succ.val) : ℝˣ) = a⁻¹ := by
    rw [hi, pow_succ, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  unfold changeDiagonal
  rw [← map_inv, diagonalUnits_mul_mul_apply, Pi.inv_apply]
  calc
    _ = (((a ^ (r - i.castSucc.val))⁻¹ * a ^ (r - i.succ.val) : ℝˣ) : ℝ) *
        u i.castSucc i.succ := by simp only [Units.val_mul]; ring
    _ = _ := by rw [hpow]

/-- The diagonal changes the real Whittaker character for `b` to the one for `b / a`. -/
theorem changeDiagonal_character (a b : ℝˣ) (u : G) :
    realWhittakerCharacter b ((changeDiagonal r a)⁻¹ * u * changeDiagonal r a) =
      realWhittakerCharacter (b * a⁻¹) u := by
  unfold realWhittakerCharacter
  simp only [changeDiagonal_inv_conj_entry, ← Finset.mul_sum]
  change ((realScaledCharacter b
      ((a⁻¹ : ℝˣ) * ∑ i : Fin r, u i.castSucc i.succ) : Circle) : ℂ) =
      ((realScaledCharacter (b * a⁻¹) (∑ i : Fin r, u i.castSucc i.succ) : Circle) : ℂ)
  rw [realScaledCharacter_apply, realScaledCharacter_apply, Units.val_mul, mul_assoc]

open scoped Matrix.Norms.Frobenius in
/-- The real matrix height is submultiplicative. -/
theorem realMatrixHeight_mul_le {n : ℕ} (x y : Langlands.GeneralLinear n ℝ) :
    realMatrixHeight (x * y) ≤ realMatrixHeight x * realMatrixHeight y := by
  simp only [RealPlaceRestriction.realMatrixHeight_eq_frobenius, Units.val_mul, mul_inv_rev]
  calc
    _ ≤ (‖x.val‖ * ‖y.val‖)^2 + (‖(y⁻¹).val‖ * ‖(x⁻¹).val‖)^2 :=
      add_le_add (pow_le_pow_left₀ (norm_nonneg _) (Matrix.frobenius_norm_mul _ _) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (Matrix.frobenius_norm_mul _ _) 2)
    _ ≤ _ := by
      nlinarith [mul_nonneg (sq_nonneg ‖x.val‖) (sq_nonneg ‖(y⁻¹).val‖),
        mul_nonneg (sq_nonneg ‖(x⁻¹).val‖) (sq_nonneg ‖y.val‖)]

/-- Precomposition with left multiplication, as a linear map on functions. -/
def leftTranslate (x : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun W g := W (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem leftTranslate_apply (x : G) (W : G → ℂ) (g : G) :
    leftTranslate x W g = W (x * g) := rfl

/-- Left translation by the inverse diagonal preserves the uniform exponent on a
coefficient map and changes its character from `b` to `b / a`. -/
theorem leftTranslate_isIntertwiner {ds : List RealBlock}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ)}
    (a b : ℝˣ) (hB : IsRealUniformWhittakerIntertwiner r ds b B) :
    IsRealUniformWhittakerIntertwiner r ds (b * a⁻¹)
      ((leftTranslate (changeDiagonal r a)⁻¹).comp B) := by
  let t := changeDiagonal r a
  let B' := (leftTranslate t⁻¹).comp B
  change IsRealUniformWhittakerIntertwiner r ds (b * a⁻¹) B'
  obtain ⟨hB, k, hk⟩ := hB
  have hgrow : ∀ f, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ‖B' f g‖ ≤ C * realMatrixHeight g ^ k := by
    intro f
    obtain ⟨C, hC, hCg⟩ := hk f
    refine ⟨C * realMatrixHeight t⁻¹ ^ k,
      mul_nonneg hC (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg _) _), fun g => ?_⟩
    change ‖B f (t⁻¹ * g)‖ ≤ _
    calc
      _ ≤ C * realMatrixHeight (t⁻¹ * g) ^ k := hCg _
      _ ≤ C * (realMatrixHeight t⁻¹ * realMatrixHeight g) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (RealPlaceRestriction.realMatrixHeight_nonneg _) (realMatrixHeight_mul_le _ _) _) hC
      _ = _ := by rw [mul_pow, mul_assoc]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, k, hgrow⟩
  · intro f u hu g
    change B f (t⁻¹ * (u * g)) = realWhittakerCharacter (b * a⁻¹) u * B f (t⁻¹ * g)
    have hN : t⁻¹ * u * t ∈ N := by
      have h := diagonal_conj_mem ((fun i : Fin (r + 1) => a ^ (r - i.val))⁻¹) u hu
      rw [map_inv, inv_inv] at h
      exact h
    have hprod : t⁻¹ * (u * g) = (t⁻¹ * u * t) * (t⁻¹ * g) := by group
    rw [hprod, hB.1 _ _ hN, changeDiagonal_character]
  · intro f
    exact (hB.2.1 f).comp contMDiff_mul_left
  · intro f
    obtain ⟨C, _, hC⟩ := hgrow f
    exact ⟨C, k, hC⟩
  · intro k f f' hf
    funext g
    change B f' (t⁻¹ * g) = B f (t⁻¹ * (g * k.val))
    rw [hB.2.2.2.1 k f f' hf]
    change B f ((t⁻¹ * g) * k.val) = _
    rw [mul_assoc]
  · intro X f f' hf
    funext g
    change B f' (t⁻¹ * g) = rightDerivative (matrixModel ℝ (r + 1)) X
      (fun h => B f (t⁻¹ * h)) g
    rw [hB.2.2.2.2 X f f' hf]
    unfold rightDerivative
    have he : (fun h : G => B f (t⁻¹ * g * h)) =
        (fun h : G => B f (t⁻¹ * (g * h))) := by
      funext h
      rw [mul_assoc]
    exact congrArg (fun F : G → ℂ =>
      mfderiv (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) F (1 : G) X) he

/-- Left translation by the inverse diagonal takes the uniform model for `ψ_b` into
that for `ψ_(b/a)`. -/
theorem leftTranslate_mem_model {ds : List RealBlock} (a b : ℝˣ)
    {W : G → ℂ} (hW : W ∈ realUniformWhittakerModel r ds b) :
    leftTranslate (changeDiagonal r a)⁻¹ W ∈ realUniformWhittakerModel r ds (b * a⁻¹) := by
  let L := leftTranslate (changeDiagonal r a)⁻¹
  have hle : realUniformWhittakerModel r ds b ≤
      (realUniformWhittakerModel r ds (b * a⁻¹)).comap L := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    exact (le_iSup₂ (f := fun B (_ : IsRealUniformWhittakerIntertwiner r ds (b * a⁻¹) B) =>
      LinearMap.range B) (L.comp B) (leftTranslate_isIntertwiner a b hB)) ⟨f, rfl⟩
  exact hle hW

end Langlands.Global.RankinSelbergGlobal.RealCharacterChange

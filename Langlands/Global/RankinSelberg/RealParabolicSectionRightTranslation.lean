import Langlands.Global.RankinSelberg.RealParabolicStandardSection
import Langlands.Global.RankinSelberg.RealGodementFourierCovariance

/-! # Right translations of compact real parabolic standard sections -/

noncomputable section

open Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.GeneralLinear Langlands.Archimedean
open Langlands.Shahidi (blockWeyl swapRank)
open Langlands.HarmonicAnalysis (rectangularLeftRightHomeomorph)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "M" => fun n => Matrix (Fin n) (Fin n) ℝ
local notation "X" => fun m n => Matrix (Fin m) (Fin n) ℝ

variable {m n : ℕ}

private theorem split_mul (u v : M (m + n)) : split (u * v) = split u * split v :=
  (Matrix.submatrix_mul_equiv u v finSumFinEquiv finSumFinEquiv finSumFinEquiv).symm

private theorem split_blockSum (a : G m) (b : G n) :
    split (blockSum (a, b)).val = Matrix.fromBlocks a.val 0 0 b.val := by
  ext i j
  cases i <;> cases j <;>
    simp [split, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

private theorem detWeight_mul (z : ℂ) {d : ℕ} (a b : G d) :
    detWeight z (a * b).val = detWeight z a.val * detWeight z b.val := by
  have ha : a.val.det ≠ 0 := (determinant a).ne_zero
  have hb : b.val.det ≠ 0 := (determinant b).ne_zero
  simp only [detWeight, Units.val_mul, Matrix.det_mul, abs_mul,
    Real.log_mul (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb), Complex.ofReal_add,
    mul_add, Complex.exp_add]

private theorem compactSection_rightLevi (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ)
    (φ : X m n → ℂ) (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (hφ : ContDiff ℝ ∞ φ)
    (hC : HasCompactSupport φ) (u : G (m + n)) (a' : G m) (b' : G n) :
    compactSection z₁ z₂ f g φ (u * blockSum (a', b')) =
      detWeight z₁ a'.val * detWeight z₂ b'.val *
      compactSection z₁ z₂ (fun a => f (a * a')) (fun b => g (b * b'))
        (fun Y => φ (a'⁻¹.val * Y * b'.val)) u := by
  by_cases hu : u ∈ parabolicCell m n
  · obtain ⟨a, b, C, Y, hcoord⟩ := exists_cellCoordinates u hu
    let Y' := a'⁻¹.val * Y * b'.val
    have hA : a'.val * Y' = Y * b'.val := by
      simp only [Y', ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul]
    have hcoord' : split (u * blockSum (a', b')).val =
        Matrix.fromBlocks (a * a').val ((a * a').val * Y') (C * a'.val)
          ((C * a'.val) * Y' + (b * b').val) := by
      rw [Units.val_mul, split_mul, hcoord, split_blockSum, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, add_zero, zero_add, Units.val_mul, Matrix.add_mul]
      simp only [Matrix.mul_assoc, hA]
    have hf' : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ (fun a => f (a * a')) :=
      hf.comp (contMDiff_id.mul contMDiff_const)
    have hg' : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun b => g (b * b')) :=
      hg.comp (contMDiff_id.mul contMDiff_const)
    have hφ' : ContDiff ℝ ∞ (fun Y : X m n => φ (a'⁻¹.val * Y * b'.val)) :=
      (RealGodement.rectangularTranslate a'⁻¹ b' (hC.toSchwartzMap hφ)).smooth'
    have hC' : HasCompactSupport (fun Y : X m n => φ (a'⁻¹.val * Y * b'.val)) :=
      hC.comp_homeomorph (rectangularLeftRightHomeomorph a'⁻¹ b')
    rw [(realParabolicCompactSection m n z₁ z₂ f g φ hf hg hφ hC).2.2 _ _ _ _ _ hcoord',
      (realParabolicCompactSection m n z₁ z₂ _ _ _ hf' hg' hφ' hC').2.2 _ _ _ _ _ hcoord,
      detWeight_mul, detWeight_mul]
    dsimp only [Y']
    ring
  · have hnew : u * blockSum (a', b') ∉ parabolicCell m n := by
      change ¬((split (u * blockSum (a', b')).val).toBlocks₁₁.det ≠ 0)
      have hz : (split u.val).toBlocks₁₁.det = 0 := not_ne_iff.mp hu
      rw [Units.val_mul, split_mul, split_blockSum, ← Matrix.fromBlocks_toBlocks (split u.val),
        Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
      simp [Matrix.det_mul, hz]
    simp [compactSection, hu, hnew]

/-- The right rectangle and right Levi actions on the normalized standard section. -/
def RealParabolicSectionRightTranslationStatement : Prop :=
  ∀ (m n : ℕ) (f : G m → ℂ) (g : G n → ℂ) (φ : X m n → ℂ),
    ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f →
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∀ (u : G (n + m)) (Z : X m n),
      standardSection f g φ (u * (swapRank m n ℝ).symm (Langlands.Shahidi.upper m n ℝ Z)) =
        standardSection f g (fun Y => φ (Y + Z)) u) ∧
    ∀ (u : G (n + m)) (a' : G m) (b' : G n),
      standardSection f g φ (u * (swapRank m n ℝ).symm (blockSum (a', b'))) =
        detWeight (-(n : ℂ) / 2) a'.val * detWeight ((m : ℂ) / 2) b'.val *
        standardSection (fun a => f (a * a')) (fun b => g (b * b'))
          (fun Y => φ (a'⁻¹.val * Y * b'.val)) u

theorem realParabolicSectionRightTranslation : RealParabolicSectionRightTranslationStatement := by
  intro m n f g φ hf hg hφ hC
  constructor
  · intro u Z
    unfold standardSection
    rw [map_mul, MulEquiv.apply_symm_apply, ← mul_assoc]
    exact (realParabolicSectionEquivariance m n _ _ f g φ hf hg hφ hC).1 _ Z
  · intro u a' b'
    unfold standardSection
    rw [map_mul, MulEquiv.apply_symm_apply, ← mul_assoc]
    exact compactSection_rightLevi _ _ f g φ hf hg hφ hC _ a' b'

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

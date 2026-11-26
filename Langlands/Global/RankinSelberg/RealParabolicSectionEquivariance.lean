import Langlands.Global.RankinSelberg.RealParabolicCompactSection
import Langlands.Representation.Shahidi.Geometry

/-! # Translation laws of compact real parabolic sections -/

noncomputable section

open Matrix Set
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.GeneralLinear Langlands.Archimedean

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "M" => fun n => Matrix (Fin n) (Fin n) ℝ
local notation "X" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "U" => fun m n => Langlands.Shahidi.upper m n ℝ

variable {m n : ℕ}

private theorem split_mul (u v : M (m + n)) : split (u * v) = split u * split v :=
  (Matrix.submatrix_mul_equiv u v finSumFinEquiv finSumFinEquiv finSumFinEquiv).symm

private theorem split_upper (Y : X m n) : split (U m n Y).val = Matrix.fromBlocks 1 Y 0 1 := by
  change ((Matrix.fromBlocks (1 : M m) Y 0 (1 : M n)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm).submatrix finSumFinEquiv finSumFinEquiv = _
  simp

private theorem mem_cell_iff (u : G (m + n)) :
    u ∈ parabolicCell m n ↔ (split u.val).toBlocks₁₁.det ≠ 0 := Iff.rfl

private theorem mul_upper_mem_iff (u : G (m + n)) (Y : X m n) :
    u * U m n Y ∈ parabolicCell m n ↔ u ∈ parabolicCell m n := by
  rw [mem_cell_iff, mem_cell_iff, Units.val_mul, split_mul, split_upper,
    ← Matrix.fromBlocks_toBlocks (split u.val), Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
  simp

/-- The leading pivot eliminates the rectangle to give two actual invertible Levi blocks. -/
theorem exists_cellCoordinates (u : G (m + n)) (hu : u ∈ parabolicCell m n) :
    ∃ (a : G m) (b : G n) (C : X n m) (Y : X m n),
      split u.val = Matrix.fromBlocks a.val (a.val * Y) C (C * Y + b.val) := by
  let A := (split u.val).toBlocks₁₁
  let B := (split u.val).toBlocks₁₂
  let C := (split u.val).toBlocks₂₁
  let D := (split u.val).toBlocks₂₂
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (mem_cell_iff u |>.mp hu))
  let a : G m := hA.unit
  have ha : a.val = A := hA.unit_spec
  let Y := a⁻¹.val * B
  have hY : a.val * Y = B := by
    dsimp only [Y]
    have h : a.val * a⁻¹.val = 1 := a.val_inv
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  let S := D - C * Y
  let v := u * U m n (-Y)
  have hv : split v.val = Matrix.fromBlocks a.val 0 C S := by
    change split (u.val * (U m n (-Y)).val) = _
    rw [split_mul, split_upper, ← Matrix.fromBlocks_toBlocks (split u.val), Matrix.fromBlocks_multiply]
    change Matrix.fromBlocks (A * 1 + B * 0) (A * -Y + B * 1) (C * 1 + D * 0)
      (C * -Y + D * 1) = Matrix.fromBlocks a.val 0 C S
    simp [← ha, hY, S, sub_eq_add_neg, add_comm]
  have hS : IsUnit S := by
    have h := congrArg Matrix.det hv
    simp only [split, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂] at h
    have hv : v.val.det ≠ 0 := (determinant v).ne_zero
    rw [h] at hv
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp hv).2)
  let b : G n := hS.unit
  have hb : b.val = S := hS.unit_spec
  refine ⟨a, b, C, Y, ?_⟩
  rw [hY, ha, hb, show C * Y + S = D by simp [S]]
  exact (Matrix.fromBlocks_toBlocks (split u.val)).symm

private theorem detWeight_mul (z : ℂ) {d : ℕ} (a b : G d) :
    detWeight z (a * b).val = detWeight z a.val * detWeight z b.val := by
  have ha : a.val.det ≠ 0 := (determinant a).ne_zero
  have hb : b.val.det ≠ 0 := (determinant b).ne_zero
  simp only [detWeight, Units.val_mul, Matrix.det_mul, abs_mul,
    Real.log_mul (abs_ne_zero.mpr ha) (abs_ne_zero.mpr hb), Complex.ofReal_add,
    mul_add, Complex.exp_add]

private theorem compactSection_rightUpper (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ)
    (φ : X m n → ℂ) (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (hφ : ContDiff ℝ ∞ φ)
    (hC : HasCompactSupport φ) (u : G (m + n)) (Z : X m n) :
    compactSection z₁ z₂ f g φ (u * U m n Z) =
      compactSection z₁ z₂ f g (fun Y => φ (Y + Z)) u := by
  by_cases hu : u ∈ parabolicCell m n
  · obtain ⟨a, b, C, Y, hcoord⟩ := exists_cellCoordinates u hu
    have hnew : split (u * U m n Z).val =
        Matrix.fromBlocks a.val (a.val * (Y + Z)) C (C * (Y + Z) + b.val) := by
      rw [Units.val_mul, split_mul, split_upper, hcoord, Matrix.fromBlocks_multiply]
      simp [Matrix.mul_add, add_comm, add_left_comm]
    have hφ' : ContDiff ℝ ∞ (fun Y : X m n => φ (Y + Z)) :=
      hφ.comp (contDiff_id.add contDiff_const)
    have hC' : HasCompactSupport (fun Y : X m n => φ (Y + Z)) :=
      hC.comp_homeomorph (Homeomorph.addRight Z)
    rw [(realParabolicCompactSection m n z₁ z₂ f g φ hf hg hφ hC).2.2 _ a b C _ hnew,
      (realParabolicCompactSection m n z₁ z₂ f g _ hf hg hφ' hC').2.2 _ a b C Y hcoord]
  · have hnew : u * U m n Z ∉ parabolicCell m n := fun h => hu ((mul_upper_mem_iff u Z).mp h)
    simp [compactSection, hu, hnew]

private theorem compactSection_leftLower (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ)
    (φ : X m n → ℂ) (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (hφ : ContDiff ℝ ∞ φ)
    (hC : HasCompactSupport φ) (v u : G (m + n)) (a' : G m) (b' : G n) (C' : X n m)
    (hv : split v.val = Matrix.fromBlocks a'.val 0 C' b'.val) :
    compactSection z₁ z₂ f g φ (v * u) =
      detWeight z₁ a'.val * detWeight z₂ b'.val *
      compactSection z₁ z₂ (fun a => f (a' * a)) (fun b => g (b' * b)) φ u := by
  by_cases hu : u ∈ parabolicCell m n
  · obtain ⟨a, b, C, Y, hcoord⟩ := exists_cellCoordinates u hu
    let C₀ := C' * a.val + b'.val * C
    have hnew : split (v * u).val =
        Matrix.fromBlocks (a' * a).val ((a' * a).val * Y) C₀ (C₀ * Y + (b' * b).val) := by
      rw [Units.val_mul, split_mul, hv, hcoord, Matrix.fromBlocks_multiply]
      simp [C₀, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, add_assoc]
    have hf' : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ (fun a => f (a' * a)) :=
      hf.comp (contMDiff_const.mul contMDiff_id)
    have hg' : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun b => g (b' * b)) :=
      hg.comp (contMDiff_const.mul contMDiff_id)
    rw [(realParabolicCompactSection m n z₁ z₂ f g φ hf hg hφ hC).2.2 _ (a' * a) (b' * b) C₀ Y hnew,
      (realParabolicCompactSection m n z₁ z₂ _ _ φ hf' hg' hφ hC).2.2 _ a b C Y hcoord,
      detWeight_mul, detWeight_mul]
    ring
  · have hnew : v * u ∉ parabolicCell m n := by
      rw [mem_cell_iff, Units.val_mul, split_mul, hv, ← Matrix.fromBlocks_toBlocks (split u.val),
        Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₁]
      have hdet : (split u.val).toBlocks₁₁.det = 0 := not_ne_iff.mp (mt (mem_cell_iff u).mpr hu)
      simp [Matrix.det_mul, hdet]
    simp [compactSection, hu, hnew]

/-- Right rectangle translation shifts the transverse test, and left block-lower translation
acts on the two Levi inputs with their determinant factors. -/
def RealParabolicSectionEquivarianceStatement : Prop :=
  ∀ (m n : ℕ) (z₁ z₂ : ℂ) (f : G m → ℂ) (g : G n → ℂ)
    (φ : X m n → ℂ), ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f →
    ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∀ (u : G (m + n)) (Z : X m n),
      compactSection z₁ z₂ f g φ (u * U m n Z) =
        compactSection z₁ z₂ f g (fun Y => φ (Y + Z)) u) ∧
    ∀ (v u : G (m + n)) (a' : G m) (b' : G n) (C' : X n m),
      split v.val = Matrix.fromBlocks a'.val 0 C' b'.val →
      compactSection z₁ z₂ f g φ (v * u) =
        detWeight z₁ a'.val * detWeight z₂ b'.val *
        compactSection z₁ z₂ (fun a => f (a' * a)) (fun b => g (b' * b)) φ u

theorem realParabolicSectionEquivariance : RealParabolicSectionEquivarianceStatement :=
  fun _ _ z₁ z₂ f g φ hf hg hφ hC =>
    ⟨compactSection_rightUpper z₁ z₂ f g φ hf hg hφ hC,
      compactSection_leftLower z₁ z₂ f g φ hf hg hφ hC⟩

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

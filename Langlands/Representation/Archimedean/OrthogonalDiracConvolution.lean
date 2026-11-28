import Langlands.Analysis.FiniteCharacterAverage
import Langlands.Representation.Archimedean.OrthogonalConvolutionDegree
import Langlands.Representation.Archimedean.OrthogonalPolynomialLipschitz

/-! # Compact Dirac testing gives an operator estimate on polynomial layers -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.OrthogonalFinitePolynomial

open RealKTypeCount
open Langlands.Analysis

universe uH

local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ

section MatrixBounds

variable {n : ℕ} {B : ℝ}

private theorem norm_inv_sub_inv_le (hB : ∀ x : O n, ‖(x : M n)‖ ≤ B)
    (x y : O n) :
    ‖(↑(x⁻¹) : M n) - (↑(y⁻¹) : M n)‖ ≤ B ^ 2 * ‖(x : M n) - (y : M n)‖ := by
  have hx : (↑(x⁻¹) : M n) * (x : M n) = 1 :=
    congrArg Subtype.val (inv_mul_cancel x)
  have hy : (y : M n) * (↑(y⁻¹) : M n) = 1 :=
    congrArg Subtype.val (mul_inv_cancel y)
  have he : (↑(x⁻¹) : M n) - (↑(y⁻¹) : M n) =
      (↑(x⁻¹) : M n) * ((y : M n) - (x : M n)) * (↑(y⁻¹) : M n) := by
    rw [mul_sub, sub_mul, mul_assoc _ (y : M n), hy, mul_one, hx, one_mul]
  rw [he]
  have hB₀ : 0 ≤ B := (norm_nonneg (1 : M n)).trans (hB 1)
  calc
    _ ≤ ‖(↑(x⁻¹) : M n) * ((y : M n) - (x : M n))‖ * ‖(↑(y⁻¹) : M n)‖ :=
      norm_mul_le _ _
    _ ≤ (‖(↑(x⁻¹) : M n)‖ * ‖(y : M n) - (x : M n)‖) * ‖(↑(y⁻¹) : M n)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (B * ‖(y : M n) - (x : M n)‖) * B :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hB x⁻¹) (norm_nonneg _)) (hB y⁻¹)
        (norm_nonneg _) (mul_nonneg hB₀ (norm_nonneg _))
    _ = _ := by rw [norm_sub_rev]; ring

private theorem norm_inv_mul_sub_inv_mul_le (hB : ∀ x : O n, ‖(x : M n)‖ ≤ B)
    (x y z : O n) :
    ‖(↑(x⁻¹ * z) : M n) - (↑(y⁻¹ * z) : M n)‖ ≤ B ^ 3 * ‖(x : M n) - (y : M n)‖ := by
  change ‖(↑(x⁻¹) : M n) * (z : M n) - (↑(y⁻¹) : M n) * (z : M n)‖ ≤ _
  rw [← sub_mul]
  calc
    _ ≤ ‖(↑(x⁻¹) : M n) - (↑(y⁻¹) : M n)‖ * ‖(z : M n)‖ := norm_mul_le _ _
    _ ≤ (B ^ 2 * ‖(x : M n) - (y : M n)‖) * B :=
      mul_le_mul (norm_inv_sub_inv_le hB x y) (hB z) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end MatrixBounds

/-- A continuous test has a Lipschitz constant `L` in the inherited matrix norm. -/
def MatrixLipschitz {n : ℕ} (L : ℝ) (ψ : C(O n, ℂ)) : Prop :=
  ∀ x y : O n, ‖ψ x - ψ y‖ ≤ L * ‖(x : M n) - (y : M n)‖

/-- A bilinear Dirac estimate for inverse-character tests gives a supremum norm
approximation estimate on each polynomial layer of the character subspace. -/
def OrthogonalDiracConvolutionStatement : Prop :=
  ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ [MeasurableSpace (O n)] [BorelSpace (O n)] [MeasurableMul (O n)]
      (μ : Measure (O n)) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
      (H : Type uH) [Group H] [Fintype H] (s : H →* O n) (χ : H →* ℂˣ)
      (κ : C(O n, ℂ)) (δ : ℝ), 0 ≤ δ →
      (∀ a : H, ∀ x : O n, κ (s a * x) = (χ a : ℂ) * κ x) →
      (∀ (ψ : C(O n, ℂ)) (L : ℝ),
        (∀ a : H, ∀ x : O n, ψ (s a * x) = (χ a : ℂ)⁻¹ * ψ x) →
        0 ≤ L → MatrixLipschitz L ψ →
        ‖(∫ x, κ x * ψ x ∂μ) - ψ 1‖ ≤ δ * (‖ψ‖ + L)) →
      ∀ (N : ℕ) (u : C(O n, ℂ)),
        (u : O n → ℂ) ∈ degreeLE n N →
        (∀ a : H, ∀ x : O n, u (s a * x) = (χ a : ℂ) * u x) →
        ‖leftConvolution μ κ u - u‖ ≤ δ * C * (1 + (N : ℝ)) ^ 2 * ‖u‖

theorem orthogonalDiracConvolution : OrthogonalDiracConvolutionStatement.{uH} := by
  intro n
  obtain ⟨A, hA, hslope⟩ := orthogonalPolynomialLipschitz n
  have hc : Continuous (fun x : O n => (x : M n)) := continuous_subtype_val
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  let B := max 1 B₀
  have hB (x : O n) : ‖(x : M n)‖ ≤ B := (hB₀ x (mem_univ x)).trans (le_max_right _ _)
  have hBpos : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨1 + A * B ^ 3, by positivity, ?_⟩
  intro _ _ _ μ _ _ H _ _ s χ κ δ hδ hκ hDirac N u hu huc
  have hnonneg : 0 ≤ δ * (1 + A * B ^ 3) * (1 + (N : ℝ)) ^ 2 * ‖u‖ := by positivity
  apply (ContinuousMap.norm_le _ hnonneg).mpr
  intro z
  let ψ : C(O n, ℂ) := u.comp ⟨fun x => x⁻¹ * z, continuous_inv.mul continuous_const⟩
  let ψ' := finiteCharacterAverage s χ ψ
  let L := A * (1 + (N : ℝ)) ^ 2 * ‖u‖ * B ^ 3
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hψ' : MatrixLipschitz L ψ' := by
    intro x y
    apply norm_sub_finiteCharacterAverage_le
    intro a
    let z' := (s a)⁻¹ * z
    change ‖u ((s a * x)⁻¹ * z) - u ((s a * y)⁻¹ * z)‖ ≤ _
    rw [mul_inv_rev, mul_inv_rev, mul_assoc, mul_assoc]
    change ‖u (x⁻¹ * z') - u (y⁻¹ * z')‖ ≤ _
    calc
      _ ≤ A * (1 + (N : ℝ)) ^ 2 * ‖u‖ *
          ‖(↑(x⁻¹ * z') : M n) - (↑(y⁻¹ * z') : M n)‖ :=
        hslope N u hu (y⁻¹ * z') (x⁻¹ * z')
      _ ≤ A * (1 + (N : ℝ)) ^ 2 * ‖u‖ * (B ^ 3 * ‖(x : M n) - (y : M n)‖) :=
        mul_le_mul_of_nonneg_left (norm_inv_mul_sub_inv_mul_le hB x y z') (by positivity)
      _ = _ := by dsimp [L]; ring
  have hψ0 : ψ' 1 = u z := by
    apply finiteCharacterAverage_apply_of_terms_eq
    intro a
    change (χ a : ℂ) * u ((s a * 1)⁻¹ * z) = _
    rw [mul_one, ← map_inv s, huc, map_inv χ, ← mul_assoc]
    simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hψnorm : ‖ψ‖ ≤ ‖u‖ := (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    fun x => u.norm_coe_le_norm (x⁻¹ * z)
  have hψ'norm := (norm_finiteCharacterAverage_le s χ ψ).trans hψnorm
  have h := hDirac ψ' L (finiteCharacterAverage_covariant s χ ψ) hL hψ'
  rw [integral_mul_finiteCharacterAverage s χ μ κ ψ hκ, hψ0] at h
  have hsum : ‖ψ'‖ + L ≤ ((1 + A * B ^ 3) * (1 + (N : ℝ)) ^ 2) * ‖u‖ := by
    have hunit : (1 : ℝ) ≤ (1 + (N : ℝ)) ^ 2 := by
      have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    calc
      _ ≤ ‖u‖ + L := add_le_add hψ'norm le_rfl
      _ ≤ (1 + (N : ℝ)) ^ 2 * ‖u‖ + L :=
        add_le_add (le_mul_of_one_le_left (norm_nonneg u) hunit) le_rfl
      _ = _ := by dsimp [L]; ring
  rw [ContinuousMap.sub_apply, leftConvolution_apply]
  calc
    _ ≤ δ * (‖ψ'‖ + L) := h
    _ ≤ δ * (((1 + A * B ^ 3) * (1 + (N : ℝ)) ^ 2) * ‖u‖) :=
      mul_le_mul_of_nonneg_left hsum hδ
    _ = _ := by ring

end Langlands.Archimedean.OrthogonalFinitePolynomial

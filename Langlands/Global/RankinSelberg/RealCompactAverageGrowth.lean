import Langlands.Global.RankinSelberg.RealNormalizedCompactAverage
import Langlands.LinearAlgebra.TriangularUnitary

/-! # Polynomial sampling bounds for real normalized compact averages -/

noncomputable section

open MeasureTheory
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealCompactAverageGrowth

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.RealPrincipalSeriesDuality (haarK)
open Langlands.Archimedean.GramFormula (realPositionExponent)
open Langlands.Archimedean.PartialJacquet (norm_principalSeriesCharacter)
open Langlands.Archimedean.RealStrictCharacterLanglandsQuotient (isSignedPower)
open Langlands.LocalFactor.Archimedean (RealBlock)
open RealNormalizedCompactAverage (contractionArguments diagonalUnits_contractionArguments contractionCharacter
  averageFactor averageScale inverseWeight oppositeMass)
open RealOppositeDilation (contractionDiagonal contractionDegree)

local instance realCompactAverageKMeasurable (j : ℕ) :
    MeasurableSpace (unitaryCompact ℝ j) := borel _
local instance realCompactAverageKBorel (j : ℕ) : BorelSpace (unitaryCompact ℝ j) := ⟨rfl⟩

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "U" => fun n => unitaryCompact ℝ n
local notation "Std" => Automorphic.realStandardKFinite

private theorem norm_contractionArguments {n : ℕ} {ε : ℝ} (hε : 0 < ε) (i : Fin n) :
    ‖(contractionArguments n hε i : ℝ)‖ = ε ^ i.val := by
  simp only [contractionArguments, Units.val_pow_eq_pow_val, Units.val_mk0, norm_pow,
    Real.norm_of_nonneg hε.le]

private def diagonalExponent (n : ℕ) (ds : List RealBlock) (i : Fin n) : ℝ :=
  (realPositionExponent ds i.val).re + ((n : ℝ) - 1) / 2 - (i.val : ℝ)

/-- The homogeneity degree of the norm of the inducing character on the contracting diagonal. -/
def contractionExponent (n : ℕ) (ds : List RealBlock) : ℝ :=
  ∑ i : Fin n, (i.val : ℝ) * diagonalExponent n ds i

theorem norm_contractionCharacter (n : ℕ) (ds : List RealBlock) {ε : ℝ} (hε : 0 < ε) :
    ‖contractionCharacter n ds hε‖ = ε ^ contractionExponent n ds := by
  rw [contractionCharacter, norm_principalSeriesCharacter (isSignedPower ds), contractionExponent,
    Real.rpow_sum_of_pos hε]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.norm_eq_abs, norm_contractionArguments, ← Real.rpow_natCast, ← Real.rpow_mul hε.le,
    diagonalExponent]

theorem norm_averageScale {n : ℕ} (c : ℝ) (hc : 0 ≤ c) {ds : List RealBlock}
    (f₀ : Std n ds) {ε : ℝ} (hε : 0 < ε) :
    ‖averageScale c f₀ hε‖ = (‖oppositeMass f₀‖ * c)⁻¹ *
      ε⁻¹ ^ ((contractionDegree n : ℝ) + contractionExponent n ds) := by
  simp only [averageScale, averageFactor, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc,
    Real.norm_of_nonneg (pow_nonneg hε.le _), norm_contractionCharacter, Real.inv_rpow hε.le,
    Real.rpow_add hε, Real.rpow_natCast, mul_inv]
  ring

/-- Jacquet's height of a unitary matrix times the contracting diagonal is polynomially bounded. -/
theorem height_unitary_mul_contractionDiagonal {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hle : ε ≤ 1)
    (k : U n) : realMatrixHeight (k.val * contractionDiagonal n hε) ≤
      (2 * (n : ℝ) ^ 2) * (ε ^ (2 * n))⁻¹ := by
  let T := (ε ^ n)⁻¹
  have hT : 1 ≤ T := (one_le_inv₀ (pow_pos hε n)).mpr (pow_le_one₀ hε.le hle)
  have hp (i : Fin n) : ε ^ i.val ≤ T := (pow_le_one₀ hε.le hle).trans hT
  have hn (i : Fin n) : (ε ^ i.val)⁻¹ ≤ T :=
    inv_anti₀ (pow_pos hε n) (pow_le_pow_of_le_one hε.le hle i.isLt.le)
  have hentry (x : U n) (i j : Fin n) : ‖x.val.val i j‖ ≤ 1 :=
    LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup x.2 i j
  let d := contractionArguments n hε
  have hd : Langlands.GeneralLinear.Iwasawa.diagonalUnits d = contractionDiagonal n hε :=
    diagonalUnits_contractionArguments n hε
  have h₁ (i j : Fin n) : ‖(k.val * contractionDiagonal n hε).val i j‖ ≤ T := by
    rw [← hd, Units.val_mul, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.mul_diagonal,
      norm_mul, norm_contractionArguments]
    exact (mul_le_mul_of_nonneg_right (hentry k i j) (pow_nonneg hε.le _)).trans
      (by simpa only [one_mul] using hp j)
  have h₂ (i j : Fin n) : ‖((k.val * contractionDiagonal n hε)⁻¹).val i j‖ ≤ T := by
    rw [← hd, mul_inv_rev, ← map_inv, Units.val_mul, Langlands.GeneralLinear.Iwasawa.diagonalUnits_val,
      Matrix.diagonal_mul, Pi.inv_apply, Units.val_inv_eq_inv_val, norm_mul, norm_inv, norm_contractionArguments]
    exact (mul_le_mul_of_nonneg_left (hentry k⁻¹ i j) (inv_nonneg.mpr (pow_nonneg hε.le _))).trans
      (by simpa only [mul_one] using hn i)
  unfold realMatrixHeight
  calc
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, 2 * T ^ 2 := by
      simp only [two_mul]
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) (h₁ i j) 2)
          (pow_le_pow_left₀ (norm_nonneg _) (h₂ i j) 2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, T,
        inv_pow, ← pow_mul, Nat.mul_comm n 2]
      ring

/-- Moderate growth of the fixed sample vector bounds the normalized Whittaker compact
projection at identity by a uniform polynomial in the inverse contraction parameter. -/
def RealCompactAverageGrowthStatement : Prop :=
  ∀ (r : ℕ) (c : ℝ) (ds : List RealBlock) (a : ℝˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)),
    0 < c → IsRealWhittakerIntertwiner r ds a B →
  ∀ (f₀ : Std (r + 1) ds), ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
    ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (f : Std (r + 1) ds) (R : ℝ),
      (∀ k : U (r + 1), ‖f.val k.val‖ ≤ R) →
      ‖averageScale c f₀ hε * ∫ k : U (r + 1), inverseWeight f k * B f₀
          (k.val * contractionDiagonal (r + 1) hε) ∂haarK (r + 1)‖ ≤
        C * R * (ε ^ M)⁻¹

theorem realCompactAverageGrowth : RealCompactAverageGrowthStatement := by
  intro r c ds a B hc hB f₀
  let n := r + 1
  obtain ⟨C₀, N₀, hC₀⟩ := hB.2.2.1 f₀
  let C₁ := max C₀ 0 * (2 * (n : ℝ) ^ 2) ^ N₀
  let C₂ := (‖oppositeMass f₀‖ * c)⁻¹
  let E := (contractionDegree n : ℝ) + contractionExponent n ds
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt E
  have hC₁ : 0 ≤ C₁ := by dsimp only [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  refine ⟨C₂ * C₁, M₀ + 2 * n * N₀, mul_nonneg hC₂ hC₁, fun ε hε hle f R hR => ?_⟩
  have hR₀ := (norm_nonneg _).trans (hR 1)
  have hScale : ‖averageScale c f₀ hε‖ ≤ C₂ * (ε ^ M₀)⁻¹ := by
    rw [norm_averageScale c hc.le f₀ hε]
    apply mul_le_mul_of_nonneg_left _ hC₂
    rw [← inv_pow, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ((one_le_inv₀ hε).mpr hle) hM₀.le
  have hSample (k : U n) : ‖B f₀ (k.val * contractionDiagonal n hε)‖ ≤ C₁ * (ε ^ (2 * n * N₀))⁻¹ := by
    have hH (g : G n) : 0 ≤ realMatrixHeight g :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    calc
      _ ≤ C₀ * realMatrixHeight (k.val * contractionDiagonal n hε) ^ N₀ := hC₀ _
      _ ≤ max C₀ 0 * ((2 * (n : ℝ) ^ 2) * (ε ^ (2 * n))⁻¹) ^ N₀ :=
        mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (hH _) (height_unitary_mul_contractionDiagonal hε hle k) _)
          (pow_nonneg (hH _) _) (le_max_right _ _)
      _ = _ := by rw [mul_pow, inv_pow, ← pow_mul, ← mul_assoc]
  have hInt : ‖∫ k : U n, inverseWeight f k * B f₀ (k.val * contractionDiagonal n hε) ∂haarK n‖ ≤
      R * (C₁ * (ε ^ (2 * n * N₀))⁻¹) := by
    refine (norm_integral_le_of_norm_le_const (μ := haarK n) (ae_of_all _ fun k => ?_)).trans
      (by simp only [probReal_univ, mul_one]; exact le_rfl)
    rw [norm_mul]
    exact mul_le_mul (hR k⁻¹) (hSample k) (norm_nonneg _) hR₀
  rw [norm_mul]
  calc
    _ ≤ (C₂ * (ε ^ M₀)⁻¹) * (R * (C₁ * (ε ^ (2 * n * N₀))⁻¹)) :=
      mul_le_mul hScale hInt (norm_nonneg _) (mul_nonneg hC₂ (inv_nonneg.mpr (pow_nonneg hε.le _)))
    _ = _ := by rw [pow_add, mul_inv]; ring

end Langlands.Global.RankinSelbergGlobal.RealCompactAverageGrowth

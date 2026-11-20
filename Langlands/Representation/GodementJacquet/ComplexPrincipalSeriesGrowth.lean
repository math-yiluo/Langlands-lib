import Langlands.Representation.GodementJacquet.ComplexPrincipalSeriesMatrixEquation
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerChangeCharacter

/-! # Polynomial height bounds for smooth complex principal series vectors -/

noncomputable section

open Set Topology
open scoped BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Global.RankinSelbergGlobal
open Langlands.Global.RankinSelbergGlobal.ComplexPlaceAnalytic
open Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange (complexMatrixHeight_mul_le)
open Langlands.LocalFactor.Archimedean

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℂ
local notation "D" => I → ℂˣ
local notation "U" => upperUnipotent n ℂ
local notation "Kc" => unitaryCompact ℂ n

private theorem real_rpow_le_ceil_abs_pow {x B : ℝ} (hx : 0 < x)
    (hB : 1 ≤ B) (hle : x ≤ B) (hinv : x⁻¹ ≤ B) (p : ℝ) :
    x ^ p ≤ B ^ (⌈|p|⌉₊ : ℕ) := by
  by_cases hp : 0 ≤ p
  · calc
      _ ≤ B ^ p := Real.rpow_le_rpow hx.le hle hp
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hB ((le_abs_self p).trans (Nat.le_ceil _))
  · calc
      _ = x⁻¹ ^ (-p) := by rw [← Real.rpow_neg_eq_inv_rpow, neg_neg]
      _ ≤ B ^ (-p) := Real.rpow_le_rpow (inv_nonneg.mpr hx.le) hinv (neg_nonneg.mpr (le_of_not_ge hp))
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hB ((neg_le_abs p).trans (Nat.le_ceil _))

private def diagonalGrowthExponent (d : I → ComplexCharacterData) (i : I) : ℝ :=
  2 * (d i).exponent.re + ((r : ℝ) - 2 * (i.val : ℝ))

private theorem norm_principalSeriesCharacter_eq (d : I → ComplexCharacterData)
    (χ : ℕ → ℂˣ → ℂ) (hχ : ∀ (i : I) (z : ℂˣ), χ i.val z = ((d i).character z : ℂ))
    (a : D) :
    ‖principalSeriesCharacter ℂ n χ a‖ =
      ∏ i, ‖(a i : ℂ)‖ ^ diagonalGrowthExponent d i := by
  unfold principalSeriesCharacter
  rw [Complex.norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hx : 0 < ‖(a i : ℂ)‖ := norm_pos_iff.mpr (a i).ne_zero
  have hdir : ‖(a i : ℂ) / (‖(a i : ℂ)‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_of_nonneg hx.le, div_self hx.ne']
  rw [hχ i, (d i).character_eq, Complex.finrank_real_complex]
  simp only [norm_mul, norm_zpow, hdir, one_zpow, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos hx _), ← Real.rpow_natCast, ← Real.rpow_mul hx.le,
    ← Real.rpow_add hx]
  congr 1
  simp only [diagonalGrowthExponent, Complex.sub_re, Complex.add_re, Complex.div_ofNat_re,
    Complex.one_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one]
  ring

private theorem norm_diagonal_coordinate_le_height (a : D) (u : U) (i : I) :
    ‖(a i : ℂ)‖ ≤ complexMatrixHeight (diagonalMatrixUnits ℂ a * u.val) ∧
      ‖(a i : ℂ)‖⁻¹ ≤ complexMatrixHeight (diagonalMatrixUnits ℂ a * u.val) := by
  let b := diagonalMatrixUnits ℂ a * u.val
  have hb : b.val i i = (a i : ℂ) := by
    rw [show b.val = Matrix.diagonal (fun j => (a j : ℂ)) * u.val.val from rfl,
      Matrix.diagonal_mul, u.property.2 i, mul_one]
  have hbi : (b⁻¹).val i i = ((a i : ℂˣ)⁻¹ : ℂ) := by
    change (((diagonalMatrixUnits ℂ a * u.val)⁻¹ : G).val) i i = _
    rw [mul_inv_rev, ← map_inv, Units.val_mul, diagonalMatrixUnits_val, Matrix.mul_diagonal]
    rw [← Subgroup.coe_inv, (u⁻¹ : U).property.2 i, one_mul]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
  constructor
  · rw [← hb]
    exact norm_entry_le_complexMatrixHeight (Nat.succ_pos r) b i i
  · have h := norm_entry_le_complexMatrixHeight (Nat.succ_pos r) b⁻¹ i i
    rw [hbi, complexMatrixHeight_inv] at h
    simpa only [norm_inv] using h

private theorem continuous_complexMatrixHeight : Continuous (fun g : G => complexMatrixHeight g) := by
  have h (i j : I) : Continuous (fun g : G => g.val i j) :=
    Units.continuous_val.matrix_elem i j
  unfold complexMatrixHeight
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((h i j).norm.pow 2).add (((h i j).comp continuous_inv).norm.pow 2)

/-- A smooth complex principal series vector with the given polar inducing
characters is bounded by one polynomial in Jacquet's height. -/
theorem exists_complexPrincipalSeries_height_bound (d : I → ComplexCharacterData)
    (χ : ℕ → ℂˣ → ℂ) (hχ : ∀ (i : I) (z : ℂˣ), χ i.val z = ((d i).character z : ℂ))
    (f : G → ℂ) (hf : f ∈ principalSeries ℂ n χ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g : G, ‖f g‖ ≤ C * complexMatrixHeight g ^ N := by
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact n
  have hfc : Continuous (fun k : Kc => f k.val) :=
    (continuous_complexPrincipalSeries hf).comp continuous_subtype_val
  have hHc : Continuous (fun k : Kc => complexMatrixHeight k.val) :=
    continuous_complexMatrixHeight.comp continuous_subtype_val
  obtain ⟨C, hC⟩ := (isCompact_range hfc.norm).bddAbove
  obtain ⟨B, hB⟩ := (isCompact_range hHc).bddAbove
  let N := ∑ i : I, ⌈|diagonalGrowthExponent d i|⌉₊
  have C₀ : 0 ≤ C := (norm_nonneg _).trans (hC (mem_range_self (1 : Kc)))
  have B₀ : 0 ≤ B := (zero_le_two.trans
    (two_le_complexMatrixHeight (Nat.succ_pos r) (1 : G))).trans (hB (mem_range_self (1 : Kc)))
  refine ⟨C * B ^ N, N, mul_nonneg C₀ (pow_nonneg B₀ _), fun g => ?_⟩
  obtain ⟨a, u, k, hk, he⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  let b : G := diagonalMatrixUnits ℂ a * u.val
  let kK : Kc := ⟨k, hk⟩
  have hek : g = b * k := he
  have hbk : b = g * k⁻¹ := by rw [hek, mul_inv_cancel_right]
  have hh : complexMatrixHeight b ≤ complexMatrixHeight g * B := by
    rw [hbk]
    exact (complexMatrixHeight_mul_le g k⁻¹).trans
      (mul_le_mul_of_nonneg_left (hB (mem_range_self kK⁻¹))
        (zero_le_two.trans (two_le_complexMatrixHeight (Nat.succ_pos r) g)))
  have hh₁ : 1 ≤ complexMatrixHeight b :=
    (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_complexMatrixHeight (Nat.succ_pos r) b)
  have hχb : ‖principalSeriesCharacter ℂ n χ a‖ ≤ complexMatrixHeight b ^ N := by
    dsimp only [N]
    rw [norm_principalSeriesCharacter_eq d χ hχ a, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) fun i _ => ?_
    have hi := norm_diagonal_coordinate_le_height a u i
    exact real_rpow_le_ceil_abs_pow (norm_pos_iff.mpr (a i).ne_zero)
      hh₁ hi.1 hi.2 (diagonalGrowthExponent d i)
  have hfvalue : f g = principalSeriesCharacter ℂ n χ a * f k := by
    rw [hek]
    exact hf.2 a u k
  rw [hfvalue, norm_mul]
  calc
    _ ≤ complexMatrixHeight b ^ N * C :=
      mul_le_mul hχb (hC (mem_range_self kK)) (norm_nonneg _) (pow_nonneg (zero_le_one.trans hh₁) _)
    _ ≤ (complexMatrixHeight g * B) ^ N * C :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hh₁) hh _) C₀
    _ = _ := by rw [mul_pow]; ring

end Langlands.GodementJacquet

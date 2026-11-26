import Langlands.Global.RankinSelberg.RealGapTriangularFourier
import Langlands.Global.RankinSelberg.RealGapLeadingSchwartz

/-! # Uniform integrable decay for the real alternate triangular columns -/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapAlternateColumnDecay

open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryCoordinates_apply upperEntryProductMeasure)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open ArchimedeanLocal (realSelfDualMeasure)
open RealGapColumnFourier (transposeColumn triangularFourier measurePreserving_entryHaar_inv)
open RealJacquetUnipotentMeasure (entryHaar)
open RealPlaceRestriction (norm_entry_le_realMatrixHeight two_le_realMatrixHeight)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "N" => fun q => Langlands.GeneralLinear.upperUnipotent (q + 1) ℝ
local notation "Entries" => fun q => UpperEntryPair (q + 1) → ℝ
local notation "Col" => fun k q => Fin (k + q + 1) → ℝ
local notation "H" => realMatrixHeight

local instance gapColumnDecayNMeasurable (q : ℕ) : MeasurableSpace (N q) := borel _
local instance gapColumnDecayNBorel (q : ℕ) : BorelSpace (N q) := ⟨rfl⟩

/-- Radial decay in the free entries of the inverse upper unipotent matrix. -/
def unipotentDecay {q : ℕ} (p : ℕ) (Z : N q) : ℝ :=
  ((1 + ‖upperEntryCoordinates (q + 1) Z⁻¹‖) ^ p)⁻¹

/-- The vectors `B^{-T}` times the padded transpose columns of `Z` control every strict upper
entry of `Z`: applying `B^T` recovers those columns at the cost of `(k + q + 1) H(B)`. -/
private theorem norm_entryCoordinates_le {k q : ℕ} (B : G (k + q + 1)) (Z : N q) :
    1 + ‖upperEntryCoordinates (q + 1) Z‖ ≤
      ((k + q + 1 : ℕ) * H B) * ∏ j : Fin q,
        (1 + ‖B⁻¹.val.transpose.mulVec (transposeColumn k q Z j)‖) := by
  let n := k + q + 1
  let L : ℝ := (n : ℝ) * H B
  let v (j : Fin q) : Col k q := B⁻¹.val.transpose.mulVec (transposeColumn k q Z j)
  let S (j : Fin q) := 1 + ‖v j‖
  have hH : 1 ≤ H B := one_le_two.trans (two_le_realMatrixHeight (Nat.succ_pos _) B)
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.succ_pos (k + q)) hH
  have hS (j : Fin q) : 1 ≤ S j := le_add_of_nonneg_right (norm_nonneg _)
  have hP : 1 ≤ ∏ j : Fin q, S j := Finset.one_le_prod₀ fun j _ => hS j
  have hRecover (j : Fin q) : B.val.transpose.mulVec (v j) = transposeColumn k q Z j := by
    dsimp only [v]
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, B.inv_mul, Matrix.transpose_one, Matrix.one_mulVec]
  change 1 + ‖upperEntryCoordinates (q + 1) Z‖ ≤ L * ∏ j : Fin q, S j
  have hh : 0 ≤ L * (∏ j : Fin q, S j) - 1 :=
    sub_nonneg.mpr (one_le_mul_of_one_le_of_one_le hL hP)
  have hn := (pi_norm_le_iff_of_nonneg (x := upperEntryCoordinates (q + 1) Z) hh).mpr (fun ij => by
    let j : Fin q := ⟨ij.val.1.val, by
      have h₂ : ij.val.2.val < q + 1 := ij.val.2.isLt
      have h₁ : ij.val.1.val < ij.val.2.val := ij.2
      omega⟩
    let i := ij.val.2.natAdd k
    have he : upperEntryCoordinates (q + 1) Z ij = transposeColumn k q Z j i := by
      rw [upperEntryCoordinates_apply, transposeColumn]
      have hki : ¬ i.val < k := by change ¬ k + ij.val.2.val < k; omega
      have hrow : ij.val.1 = j.castSucc := Fin.ext rfl
      rw [ite_eq_right hki, hrow]
      apply congrArg (Z.val.val j.castSucc)
      exact Fin.ext (by change ij.val.2.val = k + ij.val.2.val - k; omega)
    have hV : ‖(B.val.transpose.mulVec (v j)) i‖ ≤ L * ‖v j‖ := by
      rw [Matrix.mulVec, dotProduct]
      calc
        _ ≤ ∑ b : Fin n, ‖B.val.transpose i b * v j b‖ := norm_sum_le _ _
        _ ≤ ∑ _b : Fin n, H B * ‖v j‖ := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_entry_le_realMatrixHeight (Nat.succ_pos _) B b i)
            (norm_le_pi_norm _ b) (norm_nonneg _) (zero_le_one.trans hH)
        _ = _ := by simp [L, nsmul_eq_mul, mul_assoc]
    rw [he, ← hRecover j]
    refine hV.trans ?_
    have hp : S j ≤ ∏ b : Fin q, S b := by
      calc
        S j = ∏ b ∈ ({j} : Finset (Fin q)), S b := (Finset.prod_singleton S j).symm
        _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun b _ => zero_le_one.trans (hS b)) (fun b _ _ => hS b)
    have hmul := mul_le_mul_of_nonneg_left hp (zero_le_one.trans hL)
    change L * (1 + ‖v j‖) ≤ _ at hmul
    rw [mul_add, mul_one] at hmul
    linarith only [hmul, hL])
  linarith only [hn]

/-- The column Schwartz factors supply radial decay in the unipotent variables,
with a polynomial loss in the retained matrix height. -/
theorem norm_triangularFourier_le (k q : ℕ) (a : ℝˣ) (Φ : Fin q → 𝓢(Col k q, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : G (k + q + 1)) (Z : N q),
      ‖triangularFourier k q a B Φ Z‖ ≤ C * H B ^ p * unipotentDecay p Z := by
  let Ψ (j : Fin q) := RealGapColumnFourier.columnSchwartzFourier a (Φ j)
  have hΨ (j : Fin q) : (Ψ j : Col k q → ℂ) = ArchimedeanLocal.realFourierTransform a (Φ j) :=
    funext fun y => RealGapColumnFourier.columnSchwartzFourier_apply a (Φ j) y
  let S (j : Fin q) := (Finset.Iic (p, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (Ψ j)
  let C := (((k + q + 1 : ℕ) : ℝ) ^ p) * ∏ j : Fin q, (2 : ℝ) ^ p * S j
  have hS (j : Fin q) : 0 ≤ S j := apply_nonneg _ _
  refine ⟨C, mul_nonneg (by positivity) (Finset.prod_nonneg fun j _ => mul_nonneg (by positivity) (hS j)), ?_⟩
  intro B Z
  let v (j : Fin q) := B⁻¹.val.transpose.mulVec (transposeColumn k q Z⁻¹ j)
  let D := 1 + ‖upperEntryCoordinates (q + 1) Z⁻¹‖
  have hD : 0 < D := by dsimp only [D]; positivity
  have hH : 0 ≤ H B := zero_le_two.trans (two_le_realMatrixHeight (Nat.succ_pos _) B)
  have hb := pow_le_pow_left₀ hD.le (norm_entryCoordinates_le B Z⁻¹) p
  change D ^ p ≤ (((k + q + 1 : ℕ) : ℝ) * H B * ∏ j : Fin q, (1 + ‖v j‖)) ^ p at hb
  rw [triangularFourier, norm_mul, Whittaker.norm_standardCharacter, mul_one, Complex.norm_prod]
  change (∏ j : Fin q, ‖ArchimedeanLocal.realFourierTransform a (Φ j) (v j)‖) ≤ C * H B ^ p * (D ^ p)⁻¹
  simp only [← hΨ]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hD _)).mpr
  have hf (j : Fin q) : (1 + ‖v j‖) ^ p * ‖Ψ j (v j)‖ ≤ (2 : ℝ) ^ p * S j := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (p, 0)) le_rfl le_rfl (Ψ j) (v j)
    simpa only [norm_iteratedFDeriv_zero, S] using h
  calc
    _ ≤ (∏ j : Fin q, ‖Ψ j (v j)‖) * (((k + q + 1 : ℕ) : ℝ) * H B * ∏ j : Fin q, (1 + ‖v j‖)) ^ p :=
      mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (((k + q + 1 : ℕ) : ℝ) ^ p * H B ^ p) *
        ∏ j : Fin q, ((1 + ‖v j‖) ^ p * ‖Ψ j (v j)‖) := by
      rw [mul_pow, mul_pow, ← Finset.prod_pow, Finset.prod_mul_distrib]
      ring
    _ ≤ (((k + q + 1 : ℕ) : ℝ) ^ p * H B ^ p) * ∏ j : Fin q, ((2 : ℝ) ^ p * S j) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hf j))
        (mul_nonneg (by positivity) (pow_nonneg hH _))
    _ = _ := by dsimp only [C]; ring

/-- The free entry decay is integrable for an order above the real dimension. -/
theorem integrable_unipotentDecay (q p : ℕ) (μ : AdditiveHaarMeasure ℝ)
    (hp : Module.finrank ℝ (Entries q) < p) :
    Integrable (unipotentDecay (q := q) p) (entryHaar μ (q + 1)) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let η := upperEntryProductMeasure μ (q + 1)
  let e := (upperEntryCoordinates (K := ℝ) (q + 1)).toMeasurableEquiv
  have he : MeasurePreserving e.symm η (entryHaar μ (q + 1)) := ⟨e.symm.measurable, rfl⟩
  let f (x : Entries q) : ℝ := ((1 + ‖x‖) ^ p)⁻¹
  have hf : Integrable f η := by
    refine (integrable_one_add_norm (μ := η) (r := (p : ℝ)) (by exact_mod_cast hp)).congr ?_
    exact ae_of_all _ fun x => by
      change (1 + ‖x‖) ^ (-(p : ℝ)) = ((1 + ‖x‖) ^ p)⁻¹
      rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast]
  exact (measurePreserving_entryHaar_inv q μ).integrable_comp_of_integrable
    (he.symm.integrable_comp_of_integrable hf)

/-- A uniform norm majorant by an integrable entry-coordinate factor. -/
def RealGapAlternateColumnDecayStatement : Prop :=
  ∀ (k q : ℕ) (a : ℝˣ) (Φ : Fin q → 𝓢(Col k q, ℂ)),
    ∃ (p : ℕ) (C : ℝ), 0 ≤ C ∧
      Integrable (unipotentDecay (q := q) p) (entryHaar (realSelfDualMeasure a) (q + 1)) ∧
      ∀ (B : G (k + q + 1)) (Z : N q),
        ‖triangularFourier k q a B Φ Z‖ ≤ C * H B ^ p * unipotentDecay p Z

theorem realGapAlternateColumnDecay : RealGapAlternateColumnDecayStatement := by
  intro k q a Φ
  let p := Module.finrank ℝ (Entries q) + 1
  obtain ⟨C, hC, hB⟩ := norm_triangularFourier_le k q a Φ p
  exact ⟨p, C, hC, integrable_unipotentDecay q p (realSelfDualMeasure a) (Nat.lt_succ_self _), hB⟩

end Langlands.Global.RankinSelbergGlobal.RealGapAlternateColumnDecay

import Langlands.Global.RankinSelberg.RealPaddedWhittakerProduct
import Langlands.Global.RankinSelberg.RealSmoothRowCharacterAbsorption
import Langlands.Global.RankinSelberg.RealUnequalLastRowDescent

/-! # Row multiplication in one factor of a real smooth Whittaker pair -/

noncomputable section

open Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 750000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedSmoothRowAbsorption

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open CompletedProjectiveRepresentation RealPaddedExponential
open RealPaddedWhittakerProduct (oppositeScale)
open RealUnequalLastRowDescent (colEntries colUnip colUnip_val colUnip_mem character_colUnip padGL_mul_colUnip)

local notation "Height" => Langlands.Archimedean.unitHeight
local notation "row" => Langlands.RankinSelberg.lastRow

local notation "Mat" => fun n : ℕ => Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ
local notation "G" => fun n : ℕ => Langlands.GeneralLinear (n + 1) ℝ
local notation "N" => fun n : ℕ => Langlands.GeneralLinear.upperUnipotent (n + 1) ℝ

variable (n : Fin 2 → ℕ)

local notation "A" => fun i => Mat (n i)
local notation "B" => (∀ i : Fin 2, A i)
local notation "U" => Bˣ
local notation "I" => 𝓘(ℝ, B)

/-- Insert one real general linear group into its slot of a product of two groups. -/
def slot (i : Fin 2) : G (n i) →* U :=
  MulEquiv.piUnits.symm.toMonoidHom.comp (MonoidHom.mulSingle (fun j => G (n j)) i)

@[simp] theorem unitProjection_slot_self (i : Fin 2) (g : G (n i)) :
    unitProjection A i (slot n i g) = g := by
  apply Units.ext
  change (Pi.mulSingle (M := fun j => G (n j)) i g i : G (n i)).val = g.val
  rw [Pi.mulSingle_eq_same]

@[simp] theorem unitProjection_slot_of_ne {i j : Fin 2} (h : j ≠ i) (g : G (n i)) :
    unitProjection A j (slot n i g) = 1 := by
  apply Units.ext
  change (Pi.mulSingle (M := fun j => G (n j)) i g j : G (n j)).val = (1 : G (n j)).val
  rw [Pi.mulSingle_eq_of_ne h]

private def column {m : ℕ} (i : Fin 2) (x : Fin m → ℝ) : U :=
  slot n i (colUnip (r := n i) x)

private def columnCLM (m : ℕ) (i : Fin 2) : (Fin m → ℝ) →L[ℝ] B :=
  (ContinuousLinearMap.single ℝ A i).comp
    (({ toFun := colEntries (r := n i)
        map_add' := by
          intro x y
          ext p q
          by_cases hp : p.val < m <;> by_cases hq : q.val = m <;> simp [colEntries, hp, hq]
        map_smul' := by
          intro t x
          ext p q
          by_cases hp : p.val < m <;> by_cases hq : q.val = m <;> simp [colEntries, hp, hq] } :
      (Fin m → ℝ) →ₗ[ℝ] Mat (n i)).toContinuousLinearMap)

private theorem column_val {m : ℕ} (i : Fin 2) (x : Fin m → ℝ) :
    (column n i x).val = 1 + columnCLM n m i x := by
  funext j
  change (unitProjection A j (column n i x)).val = (1 : A j) + Pi.single (M := A) i (colEntries (r := n i) x) j
  by_cases h : j = i
  · subst j
    simp [column, colUnip_val]
  · simp [column, h, Pi.single_eq_of_ne]

private theorem column_inv_val {m : ℕ} (i : Fin 2) (x : Fin m → ℝ) :
    (column n i x)⁻¹.val = 1 - columnCLM n m i x := by
  funext j
  change (unitProjection A j ((column n i x)⁻¹)).val = (1 : A j) - Pi.single (M := A) i (colEntries (r := n i) x) j
  rw [map_inv]
  by_cases h : j = i
  · subst j
    rw [column, unitProjection_slot_self, Pi.single_eq_same]
    rfl
  · simp [column, h, Pi.single_eq_of_ne]

private theorem continuous_column (m : ℕ) (i : Fin 2) : Continuous (column (m := m) n i) := by
  apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
  simp_rw [Function.comp_def, column_val]
  exact continuous_const.add (columnCLM n m i).continuous

private theorem exists_columnHeight (m : ℕ) (i : Fin 2) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : Fin m → ℝ, Height (column n i x) ≤ K * max 1 ‖x‖ := by
  let C := columnCLM n m i
  let K : ℝ := 1 + ‖(1 : B)‖ + ‖C‖
  have hK : 1 ≤ K := by dsimp [K]; linarith [norm_nonneg (1 : B), norm_nonneg C]
  refine ⟨K, zero_le_one.trans hK, fun x => ?_⟩
  have hx : 1 ≤ max 1 ‖x‖ := le_max_left _ _
  have hB : ‖(1 : B)‖ + ‖C x‖ ≤ K * max 1 ‖x‖ := by
    calc
      _ ≤ ‖(1 : B)‖ * max 1 ‖x‖ + ‖C‖ * max 1 ‖x‖ :=
        add_le_add (le_mul_of_one_le_right (norm_nonneg _) hx)
          ((C.le_opNorm x).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)))
      _ ≤ _ := by rw [← add_mul]; gcongr; dsimp [K]; linarith
  unfold Langlands.Archimedean.unitHeight
  rw [column_val, column_inv_val]
  exact max_le (hK.trans (le_mul_of_one_le_right (zero_le_one.trans hK) hx))
    (max_le ((norm_add_le _ _).trans hB) ((norm_sub_le _ _).trans hB))

variable (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)] (R : ∀ i, G (n i) →* (E i →L[ℂ] E i))

local notation "D" => DerivativeSmoothVectors I (productAction A R)
local notation "act" => DerivativeSmoothVectors.representation I (productAction A R)

/-- The product action has a common polynomial bound in the unit height of the paired group. -/
theorem exists_productNorm_bound (hR : ∀ i, IsContinuousRepresentation (R i)) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ g : U, ‖productAction A R g‖ ≤ C * Height g ^ d := by
  choose C d hC hbound using fun i => exists_norm_le_unitHeight_pow ℝ (n i + 1) (R i) (hR i)
  refine ⟨∏ i, C i, ∑ i, d i, Finset.prod_nonneg fun i _ => hC i, fun g => ?_⟩
  have hh (i : Fin 2) : Height (unitProjection A i g) ≤ Height g := by
    apply max_le (Langlands.Archimedean.one_le_unitHeight g)
    apply max_le ((norm_le_pi_norm g.val i).trans (Langlands.Archimedean.norm_val_le_unitHeight g))
    rw [← map_inv]
    exact (norm_le_pi_norm (g⁻¹ : U).val i).trans (Langlands.Archimedean.norm_inv_le_unitHeight g)
  refine (norm_action_le _ g).trans ?_
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i _
  exact (hbound i (unitProjection A i g)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_le_one.trans (Langlands.Archimedean.one_le_unitHeight _)) (hh i) _) (hC i))

/-- Any Schwartz test of the row of a common leading block can be absorbed in the smooth pair
when one factor has a further column. -/
def RealPairedSmoothRowAbsorptionStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) → ∀ (a : ℝˣ) (L : D →L[ℂ] ℂ),
    (∀ (g : U) (_h : ∀ j, unitProjection A j g ∈ N (n j)) (w : D),
      L (act g w) = (∏ j, realWhittakerCharacter (oppositeScale a j) (unitProjection A j g)) * L w) →
    ∀ (m : ℕ) (hm : ∀ j, m ≤ n j) (i : Fin 2), m < n i →
      ∀ (v : D) (Φ : 𝓢((Fin (m + 1) → ℝ), ℂ)), ∃ w : D, ∀ g : G m,
        let p := padProductGL (fun j => n j + 1) (fun j => Nat.succ_le_succ (hm j)) g
        L (act p w) = L (act p v) * Φ (row g)

theorem realPairedSmoothRowAbsorption : RealPairedSmoothRowAbsorptionStatement n E R := by
  intro hR a L hL m hm i hi v Φ
  let p := padProductGL (fun j => n j + 1) (fun j => Nat.succ_le_succ (hm j))
  let j := column (m := m + 1) n i
  have hp (z : G m) (k : Fin 2) : unitProjection A k (p z) = padGL (Nat.succ_le_succ (hm k)) z := by
    apply Units.ext
    rfl
  have hComm (g : G m) (x : Fin (m + 1) → ℝ) :
      p g * j x = j (g.val *ᵥ x) * p g := by
    apply Units.ext
    funext k
    change (unitProjection A k (p g * j x)).val = (unitProjection A k (j (g.val *ᵥ x) * p g)).val
    rw [map_mul, map_mul, hp]
    by_cases hk : k = i
    · subst k
      simp only [j, column, unitProjection_slot_self]
      rw [padGL_mul_colUnip]
    · simp [j, column, hk]
  have hCov (g : G m) (x : Fin (m + 1) → ℝ) (w : D) :
      L (act (p g) (act (j x) w)) =
        (realScaledCharacter (oppositeScale a i)).complex (∑ k, x k * row g k) * L (act (p g) w) := by
    rw [← Module.End.mul_apply, ← map_mul, hComm, map_mul, Module.End.mul_apply]
    let z := g.val *ᵥ x
    have hUnip (k : Fin 2) : unitProjection A k (j z) ∈ N (n k) := by
      by_cases hk : k = i
      · subst k
        simpa only [j, column, unitProjection_slot_self] using colUnip_mem (r := n i) z
      · rw [show unitProjection A k (j z) = 1 from unitProjection_slot_of_ne n hk _]
        exact Subgroup.one_mem _
    rw [hL (j z) hUnip]
    have hChar : (∏ k, realWhittakerCharacter (oppositeScale a k) (unitProjection A k (j z))) =
        realWhittakerCharacter (oppositeScale a i) (colUnip (r := n i) z) := by
      rw [Finset.prod_eq_single i]
      · rw [show unitProjection A i (j z) = colUnip (r := n i) z from unitProjection_slot_self _ _ _]
      · intro k _ hk
        rw [show unitProjection A k (j z) = 1 from unitProjection_slot_of_ne n hk _]
        simp [realWhittakerCharacter, Fin.castSucc_lt_succ.ne]
      · simp
    have hz : z (Fin.last m) = ∑ k : Fin (m + 1), x k * row g k := by
      change (∑ k : Fin (m + 1), g.val (Fin.last m) k * x k) = _
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hChar, character_colUnip _ _ (Nat.succ_lt_succ hi), hz,
      UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply]
  obtain ⟨C, d, hC, hNorm⟩ := exists_productNorm_bound n E R hR
  exact RealSmoothRowCharacterAbsorption.realSmoothRowCharacterAbsorption (productAction A R)
    (isContinuous_productAction A R hR) (m + 1) (oppositeScale a i) j
    (continuous_column n (m + 1) i) (exists_columnHeight n (m + 1) i)
    ⟨C, d, hC, fun x => hNorm (j x)⟩ L p row hCov v Φ

end Langlands.Global.RankinSelbergGlobal.RealPairedSmoothRowAbsorption

import Langlands.Global.RankinSelberg.RealSlotStagedFamily
import Langlands.Global.RankinSelberg.RealUnequalFamilyGauge
import Langlands.Global.RankinSelberg.RealWhittakerGauge
import Langlands.Analysis.SeveralComplex.SmallExponentialBoundary

/-! # The tempered bound of the canonical Jacquet family of a slot profile -/

noncomputable section

open MeasureTheory Filter Set Metric
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SeveralComplex
open Langlands.Global.RankinSelbergGlobal.RealGodement
open Langlands.Global.RankinSelbergGlobal.RealGodementProfiles
open Langlands.Global.RankinSelbergGlobal.RealIwasawa

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLeviStages

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "K" => unitaryCompact ℝ (r + 1)

theorem neg_half_torusModularLog_le (y : Fin (r + 1) → ℝ) :
    -torusModularLog (r + 1) y / 2 ≤ (r : ℝ) * ∑ i, |y i| := by
  rw [torusModularLog_apply, ← Finset.sum_neg_distrib, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hi : (i.val : ℝ) ≤ r := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hi₀ : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have h : |(-((r + 1 : ℕ) : ℝ) + 1 + 2 * i.val) / 2| ≤ r :=
    abs_le.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  calc
    _ = (-((r + 1 : ℕ) : ℝ) + 1 + 2 * i.val) / 2 * y i := by ring
    _ ≤ |(-((r + 1 : ℕ) : ℝ) + 1 + 2 * i.val) / 2| * |y i| := by
      rw [← abs_mul]
      exact le_abs_self _
    _ ≤ _ := mul_le_mul_of_nonneg_right h (abs_nonneg _)

/-- **The tempered bound for slot profiles.** Let the exponents `z` have the half weights
`±m_q/2` as real parts on the slots and real part zero elsewhere, with differences `m_q ≠ 0` on
the slots, and let the profile have only admissible modes on the slots. Then the canonical
Jacquet family at `z` satisfies the half-modulus bound with arbitrarily small exponential loss,
uniformly on the orthogonal group. -/
theorem canonical_tempered_slot_bound (S : SlotSet (r + 1)) {p : Fin (r + 1) → Fin 2}
    {φ : U → ℂ} (hφ : IsCompactProfile p φ) (m : ℕ → ℕ) (hm : ∀ q ∈ S.starts, m q ≠ 0)
    {z : Fin (r + 1) → ℂ}
    (hz : ∀ q (hq : q ∈ S.starts), z (SlotSet.first hq) - z (SlotSet.second hq) = m q)
    (hre : ∀ i, (z i).re = halfWeights S m i)
    (hmodes : SlotModes (slotsOf S m) (standardSection z φ)) (a : ℝˣ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : Fin (r + 1) → ℝ) (k : K),
      ‖canonicalJacquetFamily a hφ z (torus y * k.val)‖ ≤
        C * Real.exp (torusModularLog (r + 1) y / 2 + ε * ∑ i, |y i|) := by
  let W := canonicalJacquetFamily a hφ
  let E := deform S z '' closedBall (0 : ℂ) 2
  have hE : IsCompact E := (isCompact_closedBall _ _).image (differentiable_deform S z).continuous
  have hW := canonicalJacquetFamily_properties a hφ
  obtain ⟨N₀, hN⟩ := RealUnequalFamily.exists_uniform_derivativeGrowth hW.2.1 hE (subset_univ E)
  obtain ⟨C, hC, hCbound⟩ := hN []
  let Sy (x : (Fin (r + 1) → ℝ) × K) : ℝ := ∑ i, |x.1 i|
  let mh (y : Fin (r + 1) → ℝ) : ℝ := torusModularLog (r + 1) y / 2
  let F (t : ℂ) (x : (Fin (r + 1) → ℝ) × K) : ℂ :=
    (Real.exp (-mh x.1) : ℂ) * W (deform S z t) (torus x.1 * x.2.val)
  have hF (x : (Fin (r + 1) → ℝ) × K) : Differentiable ℂ (fun t => F t x) :=
    ((hW.2.2.1 [] _).comp (differentiable_deform S z)).const_mul _
  have hS (x : (Fin (r + 1) → ℝ) × K) : 0 ≤ Sy x := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hNorm (t : ℂ) (x : (Fin (r + 1) → ℝ) × K) :
      ‖F t x‖ = Real.exp (-mh x.1) * ‖W (deform S z t) (torus x.1 * x.2.val)‖ := by
    change ‖(Real.exp (-mh x.1) : ℂ) * W (deform S z t) (torus x.1 * x.2.val)‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  let C₀ := C * (2 * ((r : ℝ) + 1) ^ 2) ^ N₀
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  let M := ((2 * N₀ : ℕ) : ℝ) + r
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hDisk (t : ℂ) (ht : t ∈ closedBall (0 : ℂ) 2) (x : (Fin (r + 1) → ℝ) × K) :
      ‖F t x‖ ≤ C₀ * Real.exp (M * Sy x) := by
    have htE : deform S z t ∈ E := mem_image_of_mem _ ht
    have h := hCbound (deform S z t) htE (torus x.1 * x.2.val)
    have hh := RealWhittakerGauge.realMatrixHeight_torus_mul_pow_le x.1 x.2 N₀
    rw [hNorm]
    calc
      _ ≤ Real.exp (-mh x.1) * (C * realMatrixHeight (torus x.1 * x.2.val) ^ N₀) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ ≤ Real.exp (-mh x.1) * (C₀ * Real.exp (((2 * N₀ : ℕ) : ℝ) * Sy x)) := by
        dsimp [C₀, Sy]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hC) (Real.exp_pos _).le
      _ = C₀ * Real.exp (-mh x.1 + ((2 * N₀ : ℕ) : ℝ) * Sy x) := by
        rw [Real.exp_add]
        ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₀
        have hmod : -mh x.1 ≤ (r : ℝ) * Sy x := by
          dsimp [mh, Sy]
          rw [← neg_div]
          exact neg_half_torusModularLog_le x.1
        dsimp [M]
        calc
          _ ≤ (r : ℝ) * Sy x + ((2 * N₀ : ℕ) : ℝ) * Sy x := add_le_add hmod le_rfl
          _ = _ := by ring
  have hLine (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1) :
      ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℂ, t.re = δ → |t.im| ≤ 1 → ∀ x : (Fin (r + 1) → ℝ) × K,
        ‖F t x‖ ≤ A * Real.exp ((r : ℝ) * δ * Sy x) := by
    obtain ⟨A, hA, h⟩ := norm_canonical_deform_le S hφ m hm hz hre hmodes a hδ.1
    refine ⟨A, hA, fun t ht _ x => ?_⟩
    rw [hNorm]
    calc
      _ ≤ Real.exp (-mh x.1) * (A * Real.exp (mh x.1 + (r : ℝ) * δ * Sy x)) :=
        mul_le_mul_of_nonneg_left (h t ht x.1 x.2) (Real.exp_pos _).le
      _ = _ := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  obtain ⟨B, hB, h⟩ := smallExponentialAtZero_of_rightBoundary hS hF hC₀ hM
    (Nat.cast_nonneg r) hDisk hLine ε hε
  refine ⟨B, hB, fun y k => ?_⟩
  have hb := h (y, k)
  rw [hNorm, deform_zero] at hb
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_pos (mh y)).le
  change Real.exp (mh y) * (Real.exp (-mh y) * ‖W z (torus y * k.val)‖) ≤
    Real.exp (mh y) * (B * Real.exp (ε * Sy (y, k))) at hh
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul,
    mul_left_comm, ← Real.exp_add] at hh
  exact hh

end Langlands.Global.RankinSelbergGlobal.RealLeviStages

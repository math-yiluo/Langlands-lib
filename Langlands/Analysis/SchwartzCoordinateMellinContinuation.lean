import Langlands.Analysis.SchwartzCoordinateMellinShift
import Mathlib.Analysis.Meromorphic.Basic

/-! # Meromorphic continuation of positive-coordinate Mellin integrals -/

noncomputable section

open Set Filter
open scoped Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

variable {ι : Type*} [Fintype ι]

local notation "R" => ι → ℝ
local notation "C" => ι → ℂ

private def raiseCoordinates [DecidableEq ι] (T : Finset ι) (s : C) : C :=
  fun i => if i ∈ T then s i + 1 else s i

omit [Fintype ι] in
private theorem raiseCoordinates_pos [DecidableEq ι] (T : Finset ι) {s : C}
    (hs : ∀ i, 0 < (s i).re) (i : ι) : 0 < (raiseCoordinates T s i).re := by
  by_cases hi : i ∈ T
  · simpa only [raiseCoordinates, ite_eq_left hi, Complex.add_re, Complex.one_re] using
      add_pos (hs i) zero_lt_one
  · simpa only [raiseCoordinates, ite_eq_right hi] using hs i

private theorem exists_coordinateMellin_shift [DecidableEq ι] (Φ : SchwartzMap R ℂ) (T : Finset ι) :
    ∃ Ψ : SchwartzMap R ℂ, ∀ (s : C), (∀ i, 0 < (s i).re) →
      coordinateMellin Ψ (fun i => if i ∈ T then s i + 1 else s i) =
        (∏ i ∈ T, -(s i)) * coordinateMellin Φ s := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      exact ⟨Φ, fun _ _ => by simp⟩
  | @insert i T hi ih =>
      obtain ⟨Ψ, hΨ⟩ := ih
      refine ⟨schwartzCoordinateDeriv i Ψ, fun s hs => ?_⟩
      have hraise : raiseCoordinates T s + Pi.single i 1 = raiseCoordinates (insert i T) s := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · simp [raiseCoordinates, hi]
        · simp [raiseCoordinates, Finset.mem_insert, hj]
      have h := coordinateMellin_schwartzCoordinateDeriv Ψ i (raiseCoordinates_pos T hs)
      rw [hraise] at h
      change coordinateMellin (schwartzCoordinateDeriv i Ψ) (raiseCoordinates (insert i T) s) = _
      rw [h, show raiseCoordinates T s i = s i by simp [raiseCoordinates, hi]]
      change -(s i) * coordinateMellin Ψ (fun j => if j ∈ T then s j + 1 else s j) = _
      rw [hΨ s hs, Finset.prod_insert hi, mul_assoc]

private theorem exists_coordinateMellin_round (Φ : SchwartzMap R ℂ) :
    ∃ Ψ : SchwartzMap R ℂ, ∀ (s : C), (∀ i, 0 < (s i).re) →
      coordinateMellin Ψ (fun i => s i + 1) =
        (∏ i, -(s i)) * coordinateMellin Φ s := by
  classical
  simpa only [Finset.mem_univ, ite_true] using exists_coordinateMellin_shift Φ Finset.univ

private def roundDerivative (Φ : SchwartzMap R ℂ) : SchwartzMap R ℂ :=
  (exists_coordinateMellin_round Φ).choose

private theorem coordinateMellin_roundDerivative (Φ : SchwartzMap R ℂ) {s : C}
    (hs : ∀ i, 0 < (s i).re) :
    coordinateMellin (roundDerivative Φ) (fun i => s i + 1) =
      (∏ i, -(s i)) * coordinateMellin Φ s :=
  (exists_coordinateMellin_round Φ).choose_spec s hs

private def mellinCutoffDenominator (N : ℕ) (s : C) : ℂ :=
  ∏ j ∈ Finset.range N, ∏ i, -(s i + (j : ℂ))

private def coordinateMellinAtCutoff (Φ : SchwartzMap R ℂ) (N : ℕ) (s : C) : ℂ :=
  coordinateMellin (roundDerivative^[N] Φ) (fun i => s i + (N : ℂ)) /
    mellinCutoffDenominator N s

private theorem coordinateMellinAtCutoff_succ (Φ : SchwartzMap R ℂ) {s : C} (N : ℕ)
    (hN : ∀ i, 0 < (s i + (N : ℂ)).re) :
    coordinateMellinAtCutoff Φ (N + 1) s = coordinateMellinAtCutoff Φ N s := by
  have hshift : (fun i => s i + ((N + 1 : ℕ) : ℂ)) = fun i => s i + (N : ℂ) + 1 := by
    funext i
    simp only [Nat.cast_add, Nat.cast_one, add_assoc]
  have hprod : (∏ i, -(s i + (N : ℂ))) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      neg_ne_zero.mpr (fun h => by simpa only [h, Complex.zero_re, lt_self_iff_false] using hN i)
  simp only [coordinateMellinAtCutoff, mellinCutoffDenominator, Finset.prod_range_succ,
    Function.iterate_succ_apply', hshift, coordinateMellin_roundDerivative _ hN]
  rw [mul_comm (∏ j ∈ Finset.range N, ∏ i, -(s i + (j : ℂ))),
    mul_div_mul_left _ _ hprod]

private theorem coordinateMellinAtCutoff_of_le (Φ : SchwartzMap R ℂ) {s : C}
    {M N : ℕ} (hMN : M ≤ N) (hM : ∀ i, 0 < (s i + (M : ℂ)).re) :
    coordinateMellinAtCutoff Φ N s = coordinateMellinAtCutoff Φ M s := by
  induction N, hMN using Nat.le_induction with
  | base => rfl
  | succ N hMN ih =>
      rw [coordinateMellinAtCutoff_succ Φ N, ih]
      intro i
      have hi := hM i
      simp only [Complex.add_re, Complex.natCast_re] at hi ⊢
      exact hi.trans_le (add_le_add le_rfl (Nat.cast_le.mpr hMN))

private theorem exists_mellinCutoff (s : C) : ∃ N : ℕ, ∀ i, 0 < (s i + (N : ℂ)).re := by
  have ⟨b, hb⟩ := Finite.exists_le (fun i => -(s i).re)
  have ⟨N, hN⟩ := exists_nat_gt b
  refine ⟨N, fun i => ?_⟩
  simp only [Complex.add_re, Complex.natCast_re]
  linarith [(hb i).trans_lt hN]

open Classical in
/-- The coordinate Mellin integral continued by sufficiently many integrations by parts. -/
def coordinateMellinContinuation (Φ : SchwartzMap R ℂ) (s : C) : ℂ :=
  coordinateMellinAtCutoff Φ (Nat.find (exists_mellinCutoff s)) s

private theorem coordinateMellinContinuation_eq_cutoff (Φ : SchwartzMap R ℂ) {s : C}
    (N : ℕ) (hN : ∀ i, 0 < (s i + (N : ℂ)).re) :
    coordinateMellinContinuation Φ s = coordinateMellinAtCutoff Φ N s := by
  classical
  exact (coordinateMellinAtCutoff_of_le Φ (Nat.find_min' (exists_mellinCutoff s) hN)
    (Nat.find_spec (exists_mellinCutoff s))).symm

/-- The continued integral agrees with the absolutely convergent product Mellin integral. -/
theorem coordinateMellinContinuation_eq (Φ : SchwartzMap R ℂ) {s : C}
    (hs : ∀ i, 0 < (s i).re) : coordinateMellinContinuation Φ s = coordinateMellin Φ s := by
  rw [coordinateMellinContinuation_eq_cutoff Φ 0 (by simpa using hs)]
  simp [coordinateMellinAtCutoff, mellinCutoffDenominator]

private theorem coordinateMellinContinuation_locally (Φ : SchwartzMap R ℂ)
    (c : ι → ℝ) (b : C) (z : ℂ) {N : ℕ}
    (hN : ∀ i, 0 < ((c i : ℂ) * z + (b i + (N : ℂ))).re) :
    (fun w => coordinateMellinAtCutoff Φ N (fun i => (c i : ℂ) * w + b i)) =ᶠ[𝓝 z]
      fun w => coordinateMellinContinuation Φ (fun i => (c i : ℂ) * w + b i) := by
  have h : ∀ᶠ w : ℂ in 𝓝 z, ∀ i, 0 < ((c i : ℂ) * w + (b i + (N : ℂ))).re := by
    refine eventually_all.2 fun i => ?_
    have hc : Continuous fun w : ℂ => ((c i : ℂ) * w + (b i + (N : ℂ))).re := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (hN i)
  filter_upwards [h] with w hw
  exact (coordinateMellinContinuation_eq_cutoff Φ N (by simpa only [add_assoc] using hw)).symm

private theorem analyticAt_mellinCutoffNumerator (Φ : SchwartzMap R ℂ)
    (c : ι → ℝ) (b : C) (z : ℂ) {N : ℕ}
    (hN : ∀ i, 0 < ((c i : ℂ) * z + (b i + (N : ℂ))).re) :
    AnalyticAt ℂ
      (fun w => coordinateMellin (roundDerivative^[N] Φ)
        (fun i => (c i : ℂ) * w + (b i + (N : ℂ)))) z := by
  let S : Set ℂ := {w | ∀ i, 0 < ((c i : ℂ) * w + (b i + (N : ℂ))).re}
  have hS : IsOpen S := by
    rw [show S = ⋂ i, {w : ℂ | 0 < ((c i : ℂ) * w + (b i + (N : ℂ))).re} from by
      ext w
      simp [S]]
    exact isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (by fun_prop)
  exact (differentiableOn_coordinateMellin_affine _ c _).analyticAt (hS.mem_nhds hN)

private theorem analyticAt_mellinCutoffDenominator (c : ι → ℝ) (b : C) (N : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w => mellinCutoffDenominator N (fun i => (c i : ℂ) * w + b i)) z := by
  apply Differentiable.analyticAt
  unfold mellinCutoffDenominator
  fun_prop

/-- The continued coordinate Mellin integral is meromorphic on every complex
affine line whose coordinate slopes are real. -/
theorem meromorphic_coordinateMellinContinuation_affine (Φ : SchwartzMap R ℂ)
    (c : ι → ℝ) (b : C) :
    Meromorphic (fun z => coordinateMellinContinuation Φ (fun i => (c i : ℂ) * z + b i)) := by
  intro z
  obtain ⟨N, hN⟩ := exists_mellinCutoff (fun i => (c i : ℂ) * z + b i)
  simp only [add_assoc] at hN
  have he := coordinateMellinContinuation_locally Φ c b z hN
  have h := (analyticAt_mellinCutoffNumerator Φ c b z hN).meromorphicAt.div
    (analyticAt_mellinCutoffDenominator c b N z).meromorphicAt
  apply h.congr
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with w hw
  simpa only [Pi.div_apply, coordinateMellinAtCutoff, add_assoc] using hw

/-- The only possible nonanalytic points of an affine restriction are those
where some Mellin exponent is a nonpositive integer. -/
theorem analyticAt_coordinateMellinContinuation_affine (Φ : SchwartzMap R ℂ)
    (c : ι → ℝ) (b : C) {z : ℂ}
    (hz : ∀ (i : ι) (j : ℕ), (c i : ℂ) * z + b i + (j : ℂ) ≠ 0) :
    AnalyticAt ℂ (fun w => coordinateMellinContinuation Φ (fun i => (c i : ℂ) * w + b i)) z := by
  obtain ⟨N, hN⟩ := exists_mellinCutoff (fun i => (c i : ℂ) * z + b i)
  simp only [add_assoc] at hN
  have hn : mellinCutoffDenominator N (fun i => (c i : ℂ) * z + b i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ =>
      Finset.prod_ne_zero_iff.mpr fun i _ => neg_ne_zero.mpr (hz i j)
  have h := (analyticAt_mellinCutoffNumerator Φ c b z hN).div
    (analyticAt_mellinCutoffDenominator c b N z) hn
  apply h.congr
  filter_upwards [coordinateMellinContinuation_locally Φ c b z hN] with w hw
  simpa only [Pi.div_apply, coordinateMellinAtCutoff, add_assoc] using hw

end Langlands.Analysis

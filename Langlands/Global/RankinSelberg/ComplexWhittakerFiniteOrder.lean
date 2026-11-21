import Langlands.Global.RankinSelberg.ComplexCompactDifferences
import Langlands.Global.RankinSelberg.ComplexWhittakerApproximateIdentity
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite compact difference order of complex Whittaker identity evaluation -/

noncomputable section

open Filter
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexWhittakerFiniteOrder

open Langlands.Archimedean (complexStandardRep)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactDifferences (CompactDifferenceBound compactEquivariantOrbitBound)
open ComplexCompactProbeBounds (CompactBound)
open ComplexWhittakerApproximateIdentity (complexWhittakerApproximateIdentity)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

/-- For an exact complex Whittaker intertwiner, a uniform finite-order compact right-difference
bound of the input controls its Whittaker value at the identity. -/
def ComplexWhittakerFiniteOrderStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (B : Std (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)), IsComplexWhittakerIntertwiner r ds a B →
  ∃ (J : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ (f : Std (r + 1) ds) (R : ℝ),
    CompactDifferenceBound J f R → ‖B f 1‖ ≤ D * R

set_option maxHeartbeats 1000000 in
theorem complexWhittakerFiniteOrder : ComplexWhittakerFiniteOrderStatement := by
  intro r ds a B hB
  let n := r + 1
  let ρ := complexStandardRep n ds
  let ℓ : Std n ds →ₗ[ℂ] ℂ := (LinearMap.proj 1).comp B
  obtain ⟨C, P, hC, hApprox⟩ := complexWhittakerApproximateIdentity r ds a B hB
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  let L := 1 + C
  let q : ℝ := (2 * L)⁻¹
  let M := 2 * C
  let J := P + 1
  have hL : 0 < L := by dsimp only [L]; positivity
  have hq : 0 < q := by dsimp only [q]; positivity
  have hq₁ : q ≤ 1 := by
    have h : 1 ≤ 2 * L := by dsimp only [L]; linarith
    exact inv_le_one_of_one_le₀ h
  have hLq : L * q = 1 / 2 := by
    dsimp only [q]
    field_simp
  choose A hA hValue hError hSample using fun i : ℕ => hApprox (q ^ i) (pow_pos hq i)
    (pow_le_one₀ hq.le hq₁)
  let T : ℕ → Module.End ℂ (Std n ds) :=
    Nat.rec 1 (fun i Ti => (1 - A i) * Ti)
  have hT (i : ℕ) (k : K n) (f : Std n ds) : T i (ρ k f) = ρ k (T i f) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      change T i (ρ k f) - A i (T i (ρ k f)) = ρ k (T i f - A i (T i f))
      rw [ih, hA, map_sub]
  let coefficient (i : ℕ) := C * L ^ i * ((q ^ i) ^ P)⁻¹
  let H := ∑ i ∈ Finset.range J, coefficient i
  let E := C * M ^ J * ((q ^ J) ^ P)⁻¹
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hH : 0 ≤ H := Finset.sum_nonneg fun i _ => by dsimp only [coefficient]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨J, H + 2 * E, by positivity, fun f R hR => ?_⟩
  have hR₀ : 0 ≤ R := hR.constant_nonneg
  let v (i : ℕ) := T i f
  have hv₀ : v 0 = f := rfl
  have hv (i : ℕ) : v (i + 1) = v i - A i (v i) := rfl
  have crude (m : ℕ) : CompactDifferenceBound J (v m) (L ^ m * R) := by
    induction m with
    | zero => simpa only [hv₀, pow_zero, one_mul] using hR
    | succ m ih =>
      rw [hv, pow_succ, mul_comm (L ^ m), mul_assoc]
      exact ih.residual (A m) (hA m) (hValue m)
  have gain (j : ℕ) (hj : j ≤ J) (m : ℕ) :
      CompactDifferenceBound (J - j) (v (m + j)) (L ^ m * (M * q ^ m) ^ j * R) := by
    induction j with
    | zero => simpa only [Nat.sub_zero, Nat.add_zero, pow_zero, mul_one] using crude m
    | succ j ih =>
      have hb := ih (Nat.le_of_succ_le hj)
      rw [show J - j = J - (j + 1) + 1 by omega] at hb
      change CompactDifferenceBound (J - (j + 1)) (v ((m + j) + 1))
        (L ^ m * (M * q ^ m) ^ (j + 1) * R)
      rw [hv]
      apply (hb.residual_succ (A (m + j)) (hA (m + j)) (hError (m + j))).mono
      have hqj : q ^ (m + j) ≤ q ^ m := by
        rw [pow_add]
        exact mul_le_of_le_one_right (pow_nonneg hq.le _) (pow_le_one₀ hq.le hq₁)
      calc
        _ ≤ 2 * C * q ^ m * (L ^ m * (M * q ^ m) ^ j * R) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hqj (by positivity)) (by positivity)
        _ = _ := by rw [pow_succ]; dsimp only [M]; ring
  have small (m : ℕ) : CompactBound (v (m + J)) (L ^ m * (M * q ^ m) ^ J * R) :=
    (gain J le_rfl m).value
  have rate (m : ℕ) : L ^ m * (M * q ^ m) ^ J * R =
      M ^ J * R * ((1 / 2 : ℝ) ^ m * (q ^ m) ^ P) := by
    calc
      _ = M ^ J * R * ((L ^ m * q ^ m) * (q ^ m) ^ P) := by
        rw [mul_pow, show (q ^ m) ^ J = (q ^ m) ^ P * q ^ m from pow_succ _ _]
        ring
      _ = _ := by rw [← mul_pow, hLq]
  have sampleTail (m : ℕ) : ‖ℓ (A (m + J) (v (m + J)))‖ ≤ E * R * (1 / 2 : ℝ) ^ m := by
    calc
      _ ≤ C * (L ^ m * (M * q ^ m) ^ J * R) * ((q ^ (m + J)) ^ P)⁻¹ :=
        hSample (m + J) _ _ (small m)
      _ = E * R * (1 / 2 : ℝ) ^ m * ((q ^ m) ^ P * ((q ^ m) ^ P)⁻¹) := by
        rw [rate m, pow_add q m J, mul_pow (q ^ m) (q ^ J) P,
          mul_inv_rev ((q ^ m) ^ P) ((q ^ J) ^ P)]
        dsimp only [E]
        ring
      _ = _ := by rw [mul_inv_cancel₀ (by positivity), mul_one]
  have step (i : ℕ) : ‖ℓ f - ℓ (v (i + 1))‖ ≤ ‖ℓ f - ℓ (v i)‖ + ‖ℓ (A i (v i))‖ := by
    rw [hv, map_sub, sub_sub_eq_add_sub, add_sub_right_comm]
    exact norm_add_le _ _
  have head (j : ℕ) : ‖ℓ f - ℓ (v j)‖ ≤ (∑ i ∈ Finset.range j, coefficient i) * R := by
    induction j with
    | zero => simp [hv₀]
    | succ j ih =>
      have hs : ‖ℓ (A j (v j))‖ ≤ coefficient j * R := by
        exact (hSample j _ _ (crude j).value).trans_eq (by dsimp only [coefficient]; ring)
      exact (step j).trans ((add_le_add ih hs).trans_eq (by rw [Finset.sum_range_succ, add_mul]))
  have tail (m : ℕ) : ‖ℓ f - ℓ (v (m + J))‖ ≤ (H + 2 * E * (1 - (1 / 2 : ℝ) ^ m)) * R := by
    induction m with
    | zero => simpa only [Nat.zero_add, pow_zero, sub_self, mul_zero, add_zero] using head J
    | succ m ih =>
      rw [Nat.succ_add]
      exact (step (m + J)).trans ((add_le_add ih (sampleTail m)).trans_eq (by rw [pow_succ]; ring))
  obtain ⟨S, hS, hOrbit⟩ := compactEquivariantOrbitBound n ds f ℓ
  have residual (m : ℕ) : ‖ℓ (v (m + J))‖ ≤ (S * M ^ J * R) * (1 / 2 : ℝ) ^ m := by
    calc
      _ ≤ S * (L ^ m * (M * q ^ m) ^ J * R) := hOrbit (T (m + J)) (hT (m + J)) _ (small m)
      _ = (S * M ^ J * R * (1 / 2 : ℝ) ^ m) * (q ^ m) ^ P := by rw [rate]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) (pow_le_one₀ (pow_nonneg hq.le _)
        (pow_le_one₀ hq.le hq₁))
  have hlim : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim' : Tendsto (fun m : ℕ => (H + 2 * E) * R + (S * M ^ J * R) * (1 / 2 : ℝ) ^ m)
      atTop (𝓝 ((H + 2 * E) * R)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)
  apply ge_of_tendsto' hlim'
  intro m
  change ‖ℓ f‖ ≤ _
  have hCut : H + 2 * E * (1 - (1 / 2 : ℝ) ^ m) ≤ H + 2 * E := by
    exact add_le_add le_rfl
      (mul_le_of_le_one_right (by positivity) (sub_le_self 1 (by positivity)))
  calc
    _ ≤ ‖ℓ f - ℓ (v (m + J))‖ + ‖ℓ (v (m + J))‖ := by
      simpa only [sub_add_cancel] using norm_add_le (ℓ f - ℓ (v (m + J))) (ℓ (v (m + J)))
    _ ≤ _ := add_le_add ((tail m).trans (mul_le_mul_of_nonneg_right hCut hR₀)) (residual m)

end Langlands.Global.RankinSelbergGlobal.ComplexWhittakerFiniteOrder

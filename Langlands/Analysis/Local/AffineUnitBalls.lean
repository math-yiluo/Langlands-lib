import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-! # Compact open unit subgroups in additive coordinates -/

noncomputable section

namespace Langlands.Analysis

open Metric Set _root_.Topology

universe u v w

variable {F : Type u} [NontriviallyNormedField F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R]
  {X : Type w} [NormedAddCommGroup X] [NormedSpace F X] [IsUltrametricDist X]

private theorem norm_inverse_unit_ball (e : X ≃L[F] R) (r c : ℝ) (hc : 0 ≤ c)
    (hcr : c * r < 1)
    (hm : ∀ a b : R, ‖e.symm (a * b)‖ ≤ c * (‖e.symm a‖ * ‖e.symm b‖))
    (u : Rˣ) (hu : ‖e.symm (u.val - 1)‖ ≤ r) :
    ‖e.symm ((u⁻¹ : Rˣ).val - 1)‖ ≤ r := by
  let a := u.val - 1
  let b := (u⁻¹ : Rˣ).val - 1
  have hEq : b = -a - a * b := by
    have h : a + b + a * b = 0 := by
      dsimp only [a, b]
      have hh : u.val * (u⁻¹ : Rˣ).val = 1 := u.val_inv
      calc
        _ = u.val * (u⁻¹ : Rˣ).val - 1 := by noncomm_ring
        _ = 0 := by rw [hh, sub_self]
    calc
      b = (a + b + a * b) - a - a * b := by abel
      _ = -a - a * b := by rw [h, zero_sub]
  by_contra! hb
  have hpos : 0 < ‖e.symm b‖ := (norm_nonneg (e.symm a)).trans_lt (hu.trans_lt hb)
  have hlt : c * (‖e.symm a‖ * ‖e.symm b‖) < ‖e.symm b‖ := by
    rw [← mul_assoc]
    exact mul_lt_of_lt_one_left hpos ((mul_le_mul_of_nonneg_left hu hc).trans_lt hcr)
  have ht : ‖e.symm b‖ ≤ max ‖e.symm a‖ ‖e.symm (a * b)‖ := by
    conv_lhs => rw [hEq]
    rw [map_sub, map_neg, sub_eq_add_neg]
    simpa only [norm_neg] using
      (IsUltrametricDist.norm_add_le_max (-e.symm a) (-e.symm (a * b)))
  exact (not_lt_of_ge ht) (max_lt (hu.trans_lt hb) ((hm a b).trans_lt hlt))

private theorem norm_mul_unit_ball (e : X ≃L[F] R) (r c : ℝ) (hr : 0 ≤ r) (hc : 0 ≤ c)
    (hcr : c * r < 1)
    (hm : ∀ a b : R, ‖e.symm (a * b)‖ ≤ c * (‖e.symm a‖ * ‖e.symm b‖))
    (u v : Rˣ) (hu : ‖e.symm (u.val - 1)‖ ≤ r) (hv : ‖e.symm (v.val - 1)‖ ≤ r) :
    ‖e.symm ((u * v).val - 1)‖ ≤ r := by
  let a := u.val - 1
  let b := v.val - 1
  have hEq : (u * v).val - 1 = a + b + a * b := by
    rw [Units.val_mul]
    dsimp only [a, b]
    noncomm_ring
  rw [hEq, map_add, map_add]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  refine max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)) ?_
  calc
    _ ≤ c * (‖e.symm a‖ * ‖e.symm b‖) := hm a b
    _ ≤ c * (r * r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hu hv (norm_nonneg _) hr) hc
    _ ≤ r := by rw [← mul_assoc]; exact mul_le_of_le_one_left hr hcr.le

/-- Sufficiently small balls in any ultrametric linear coordinates at the
identity are the affine matrix images of compact open subgroups of units. -/
theorem exists_compactOpenSubgroup_affineBall [CompleteSpace R] [ProperSpace X] (e : X ≃L[F] R) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∃ U : OpenSubgroup Rˣ, IsCompact (U : Set Rˣ) ∧
        Set.range (fun u : U => (u : Rˣ).val - 1) = e '' closedBall 0 r := by
  let a := ‖(e : X →L[F] R)‖
  let b := ‖(e.symm : R →L[F] X)‖
  let c := b * a * a
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hm (p q : R) : ‖e.symm (p * q)‖ ≤ c * (‖e.symm p‖ * ‖e.symm q‖) := by
    have hb (x : R) : ‖x‖ ≤ a * ‖e.symm x‖ := by
      simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
        (e : X →L[F] R).le_opNorm (e.symm x)
    calc
      _ ≤ b * ‖p * q‖ := (e.symm : R →L[F] X).le_opNorm _
      _ ≤ b * (‖p‖ * ‖q‖) := mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ b * ((a * ‖e.symm p‖) * (a * ‖e.symm q‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hb p) (hb q) (norm_nonneg _) (by positivity))
          (norm_nonneg _)
      _ = _ := by dsimp only [c]; ring
  obtain ⟨r₀, hr₀, hsmall⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧
      c * r₀ < 1 ∧ ∀ x ∈ closedBall (0 : X) r₀, IsUnit (1 + e x) := by
    have hcont := (continuous_const.add e.continuous : Continuous (fun x : X => (1 : R) + e x))
    have hU : {x : X | IsUnit (1 + e x)} ∈ 𝓝 0 :=
      (Units.isOpen.preimage hcont).mem_nhds (by simp)
    have hC : {r : ℝ | c * r < 1} ∈ 𝓝 0 :=
      (isOpen_lt (continuous_const.mul continuous_id) continuous_const).mem_nhds (by simp)
    obtain ⟨rU, hrU, hru⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨rC, hrC, hrc⟩ := Metric.mem_nhds_iff.mp hC
    let r₀ := min rU rC / 2
    have hr_min : 0 < min rU rC := lt_min hrU hrC
    have hlt : r₀ < min rU rC := half_lt_self hr_min
    refine ⟨r₀, half_pos hr_min, ?_, ?_⟩
    · apply hrc
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr_min)]
      exact hlt.trans_le (min_le_right _ _)
    · intro x hx
      exact hru (closedBall_subset_ball (hlt.trans_le (min_le_left _ _)) hx)
  refine ⟨r₀, hr₀, fun r hr hrle => ?_⟩
  have hcr : c * r < 1 := (mul_le_mul_of_nonneg_left hrle hc).trans_lt hsmall.1
  let G : Subgroup Rˣ :=
    { carrier := {u | ‖e.symm (u.val - 1)‖ ≤ r}
      one_mem' := by simp [hr.le]
      mul_mem' := fun {u v} hu hv => norm_mul_unit_ball e r c hr.le hc hcr hm u v hu hv
      inv_mem' := fun {u} hu => norm_inverse_unit_ball e r c hc hcr hm u hu }
  let affine : Rˣ → X := fun u => e.symm (u.val - 1)
  have ha : IsOpenEmbedding affine := e.symm.toHomeomorph.isOpenEmbedding.comp
    ((Homeomorph.subRight (1 : R)).isOpenEmbedding.comp Units.isOpenEmbedding_val)
  have hG : (G : Set Rˣ) = affine ⁻¹' closedBall (0 : X) r := by
    ext u
    rw [mem_preimage, mem_closedBall, dist_zero_right]
    rfl
  let U : OpenSubgroup Rˣ := ⟨G, by
    change IsOpen (G : Set Rˣ)
    rw [hG]
    exact IsOpen.preimage ha.continuous (IsUltrametricDist.isOpen_closedBall _ hr.ne')⟩
  have hsurj : affine '' (U : Set Rˣ) = closedBall (0 : X) r := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact show u ∈ affine ⁻¹' closedBall 0 r from hG ▸ hu
    · intro hx
      have hu := hsmall.2 x (closedBall_subset_closedBall hrle hx)
      have hEq : affine hu.unit = x := by
        change e.symm (hu.unit.val - 1) = x
        rw [hu.unit_spec, add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply]
      have huU : hu.unit ∈ (U : Set Rˣ) := by
        change hu.unit ∈ (G : Set Rˣ)
        rw [hG]
        change affine hu.unit ∈ closedBall (0 : X) r
        rwa [hEq]
      exact ⟨hu.unit, huU, hEq⟩
  refine ⟨U, ha.isEmbedding.isCompact_iff.mpr (hsurj.symm ▸ isCompact_closedBall 0 r), ?_⟩
  have hEq (u : Rˣ) : u.val - 1 = e (affine u) := (e.apply_symm_apply _).symm
  simp_rw [hEq]
  rw [show (fun u : U => e (affine u.val)) = e ∘ (affine ∘ Subtype.val) from rfl,
    Set.range_comp, Set.range_comp, Subtype.range_coe, hsurj]

end Langlands.Analysis

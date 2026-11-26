import Langlands.Analysis.Local.WeylChartTorus

/-! # The product decomposition of the coordinate subgroup -/

set_option linter.unusedSectionVars false

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology MeasureTheory Measure Langlands.QuotientIntegration
open scoped NNReal ENNReal

universe u v

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [ProperSpace F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R] [FiniteDimensional F R] [CompleteSpace R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R]

theorem isUnit_one_add_of_norm_lt_one {a : R} (h : ‖a‖ < 1) : IsUnit (1 + a) := by
  have h' : ‖-a‖ < 1 := by rwa [norm_neg]
  have hu := (Units.oneSub (-a) h').isUnit
  rwa [Units.val_oneSub, sub_neg_eq_add] at hu

theorem coordCLE_symm_transverse {γ : Rˣ} (hγ : IsRegularPosition F γ)
    (y : LinearMap.range (defect F γ)) : (coordCLE hγ).symm (y : R) = (y, 0) := by
  apply (coordCLE hγ).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, coordCLE_apply]
  simp

theorem norm_coordCLE_symm_transverse {γ : Rˣ} (hγ : IsRegularPosition F γ)
    (y : LinearMap.range (defect F γ)) : ‖(coordCLE hγ).symm (y : R)‖ = ‖y‖ := by
  rw [coordCLE_symm_transverse, Prod.norm_def, norm_zero]
  exact max_eq_left (norm_nonneg _)

section Units

variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
include hr

theorem isUnit_one_add_transverse {y : LinearMap.range (defect F γ)} (hy : ‖y‖ ≤ r) :
    IsUnit (1 + (y : R)) :=
  isUnit_one_add_of_norm_lt_one (by simpa using hy.trans_lt hr.lt_one)

theorem isUnit_one_add_central {s : centralizerAlg F γ} (hs : ‖s‖ ≤ r) :
    IsUnit (1 + (s : R)) :=
  isUnit_one_add_of_norm_lt_one (by simpa using hs.trans_lt hr.lt_one)

theorem unitOf_transverse_mem {y : LinearMap.range (defect F γ)} (hy : ‖y‖ ≤ r) :
    unitOf (1 + (y : R)) ∈ unitBall hγ hr := by
  rw [mem_unitBall, val_unitOf (isUnit_one_add_transverse hγ hr hy), add_sub_cancel_left,
    norm_coordCLE_symm_transverse]
  exact hy

theorem unitOf_central_mem {s : centralizerAlg F γ} (hs : ‖s‖ ≤ r) :
    unitOf (1 + (s : R)) ∈ unitBall hγ hr := by
  rw [mem_unitBall, val_unitOf (isUnit_one_add_central hγ hr hs), add_sub_cancel_left,
    norm_coordCLE_symm_centralizer]
  exact hs

theorem val_unitOf_mul_unitOf {x : Coord F γ} (hx : ‖x‖ ≤ r) :
    ((unitOf (1 + (x.1 : R)) * unitOf (1 + (x.2 : R)) : Rˣ) : R) = 1 + productMap γ x := by
  have h1 : ‖x.1‖ ≤ r := (norm_fst_le x).trans hx
  have h2 : ‖x.2‖ ≤ r := (norm_snd_le x).trans hx
  rw [Units.val_mul, val_unitOf (isUnit_one_add_transverse hγ hr h1),
    val_unitOf (isUnit_one_add_central hγ hr h2), productMap]
  abel

end Units

section Decomposition

variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
  (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
include hr hbij

/-- Every element of the coordinate subgroup is a product of a transverse and a central
unit with small coordinates. -/
theorem exists_eq_unitOf_mul_unitOf (k : Rˣ) (hk : k ∈ unitBall hγ hr) :
    ∃ x : Coord F γ, ‖x‖ ≤ r ∧ k = unitOf (1 + (x.1 : R)) * unitOf (1 + (x.2 : R)) := by
  have hk' : ((k : R) - 1) ∈ coordCLE hγ '' closedBall 0 r := by
    refine ⟨(coordCLE hγ).symm ((k : R) - 1), ?_, by simp⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk
  obtain ⟨x, hx, hxk⟩ := hbij.surjOn hk'
  have hxr : ‖x‖ ≤ r := by simpa using hx
  refine ⟨x, hxr, Units.ext ?_⟩
  rw [val_unitOf_mul_unitOf hγ hr hxr, hxk]
  abel

/-- The decomposition into transverse and central units is unique on the coordinate ball. -/
theorem eq_of_unitOf_mul_unitOf_eq {x x' : Coord F γ} (hx : ‖x‖ ≤ r) (hx' : ‖x'‖ ≤ r)
    (h : unitOf (1 + (x.1 : R)) * unitOf (1 + (x.2 : R)) =
      unitOf (1 + (x'.1 : R)) * unitOf (1 + (x'.2 : R))) : x = x' := by
  have hv := congrArg Units.val h
  rw [val_unitOf_mul_unitOf hγ hr hx, val_unitOf_mul_unitOf hγ hr hx'] at hv
  have hv' := add_left_cancel hv
  exact hbij.injOn (by simpa using hx) (by simpa using hx') hv'

end Decomposition

end Langlands.Analysis.WeylChart

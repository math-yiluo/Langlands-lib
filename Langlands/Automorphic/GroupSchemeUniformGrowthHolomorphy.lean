import Langlands.Automorphic.GroupSchemeUniformGrowthOperators
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! # Norm-holomorphic derivative coordinates of growth-space curves -/

noncomputable section

open Filter Set Metric
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]
  {f : ℂ → B} {U : Set ℂ}

private theorem continuousOn_of_dual_differentiable (hU : IsOpen U)
    (hf : ∀ ℓ : B →L[ℂ] ℂ, DifferentiableOn ℂ (fun z => ℓ (f z)) U) :
    ContinuousOn f U := by
  intro z hz
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hU z hz
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : closedBall z r ⊆ U := (closedBall_subset_ball (half_lt_self hR)).trans hsub
  let g (w : closedBall z r) := NormedSpace.inclusionInDoubleDual ℂ B (f w)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := g) (fun ℓ => by
    obtain ⟨c, hc⟩ := (isCompact_closedBall z r).exists_bound_of_continuousOn
      ((hf ℓ).mono hclosed).continuousOn
    exact ⟨c, fun w => hc w w.property⟩)
  have hbound (w : ℂ) (hw : w ∈ closedBall z r) : ‖f w‖ ≤ C := by
    rw [← (NormedSpace.inclusionInDoubleDualLi (E := B) ℂ).norm_map (f w)]
    exact hC ⟨w, hw⟩
  have hC₀ := (norm_nonneg _).trans (hbound z (mem_closedBall_self hr.le))
  have hLip (w : ℂ) (hw : w ∈ ball z r) : ‖f w - f z‖ ≤ (2 * C / r) * ‖w - z‖ := by
    refine NormedSpace.norm_le_dual_bound ℂ _ (by positivity) fun ℓ => ?_
    have hmap : MapsTo (fun t => ℓ (f t)) (ball z r) (closedBall (ℓ (f z)) (2 * C * ‖ℓ‖)) := by
      intro t ht
      rw [mem_closedBall, dist_eq_norm, ← map_sub]
      calc
        _ ≤ ‖ℓ‖ * ‖f t - f z‖ := ℓ.le_opNorm _
        _ ≤ ‖ℓ‖ * (C + C) := mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans (add_le_add (hbound _ (ball_subset_closedBall ht))
            (hbound _ (mem_closedBall_self hr.le)))) (norm_nonneg _)
        _ = 2 * C * ‖ℓ‖ := by ring
    have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball
      ((hf ℓ).mono (ball_subset_closedBall.trans hclosed)) hmap hw
    rw [dist_eq_norm, dist_eq_norm, ← map_sub] at h
    calc
      _ ≤ 2 * C * ‖ℓ‖ / r * ‖w - z‖ := h
      _ = (2 * C / r * ‖w - z‖) * ‖ℓ‖ := by ring
  apply ContinuousAt.continuousWithinAt
  apply tendsto_sub_nhds_zero_iff.mp
  have hO : (fun w => f w - f z) =O[𝓝 z] (fun w => w - z) := by
    apply Asymptotics.IsBigO.of_bound (2 * C / r)
    filter_upwards [ball_mem_nhds z hr] with w hw using hLip w hw
  exact hO.trans_tendsto (tendsto_sub_nhds_zero_iff.mpr tendsto_id)

open Complex
open scoped Real Interval in
/-- On an open subset of the complex plane, a Banach-valued function is analytic
if all its continuous linear scalar tests are complex differentiable. -/
theorem analyticOnNhd_of_dual_differentiable [CompleteSpace B] (hU : IsOpen U)
    (hf : ∀ ℓ : B →L[ℂ] ℂ, DifferentiableOn ℂ (fun z => ℓ (f z)) U) :
    AnalyticOnNhd ℂ f U := by
  intro z hz
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hU z hz
  let r : ℝ := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : closedBall z r ⊆ U := (closedBall_subset_ball (half_lt_self hR)).trans hsub
  have hi : CircleIntegrable f z r := ContinuousOn.circleIntegrable hr.le
    ((continuousOn_of_dual_differentiable hU hf).mono (sphere_subset_closedBall.trans hclosed))
  let C (w : ℂ) := (2 * π * I : ℂ)⁻¹ • ∮ t in C(z, r), (t - w)⁻¹ • f t
  have hnot (w : ℂ) (hw : w ∈ ball z r) : w ∉ sphere z |r| := by
    rw [abs_of_pos hr]
    exact fun h => (mem_ball.mp hw).ne (mem_sphere.mp h)
  have hEq (w : ℂ) (hw : w ∈ ball z r) : C w = f w := by
    apply sub_eq_zero.mp
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro ℓ
    have hInt : CircleIntegrable (fun t => (t - w)⁻¹ • f t) z r := by
      simpa only [zpow_neg_one] using hi.sub_zpow_smul (-1) (hnot w hw)
    have hMap : (∮ t in C(z, r), (t - w)⁻¹ • ℓ (f t)) =
        ℓ (∮ t in C(z, r), (t - w)⁻¹ • f t) := by
      simpa only [circleIntegral, map_smul] using ℓ.intervalIntegral_comp_comm hInt.out
    rw [map_sub, show ℓ (C w) = (2 * π * I : ℂ)⁻¹ •
        ℓ (∮ t in C(z, r), (t - w)⁻¹ • f t) from map_smul _ _ _,
      ← hMap, ((hf ℓ).mono hclosed).circleIntegral_sub_inv_smul hw,
      inv_smul_smul₀ two_pi_I_ne_zero, sub_self]
  have hDiff : DifferentiableOn ℂ C (ball z r) := by
    intro w hw
    exact ((hasDerivAt_circleIntegral_sub_inv_smul hi (hnot w hw)).const_smul
      (2 * π * I : ℂ)⁻¹).differentiableAt.differentiableWithinAt
  exact (hDiff.congr fun w hw => (hEq w hw).symm).analyticAt (ball_mem_nhds z hr)

end Langlands.Analysis

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {N d : ℕ} (rho : Langlands.GroupScheme.MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (hN : 0 < N) (hrho : Langlands.GroupScheme.IsClosedSubgroup rho)
  (R : ℝ) (L : Subgroup (FiniteAdelicGroupPoints F G))

local notation "V" => UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L
local notation "UEA" => AdelicEnvelopingAlgebra F G hsmooth
local notation "B" => lp (fun _ : AdelicGroupPoints F G => ℂ) ∞

/-- A weakly holomorphic curve in the growth space is norm-analytic in each
weighted derivative coordinate. -/
theorem analyticOnNhd_weightedDerivative {f : ℂ → V} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ test : V →L[ℂ] ℂ, DifferentiableOn ℂ (fun z => test (f z)) U)
    (a : UEA) :
    AnalyticOnNhd ℂ (weightedDerivative F G rho hsmooth hcalc hN hrho R L a ∘ f) U :=
  Langlands.Analysis.analyticOnNhd_of_dual_differentiable hU
    (fun test : B →L[ℂ] ℂ =>
      hf (test.comp (weightedDerivativeCLM F G rho hsmooth hcalc hN hrho R L a)))

/-- The factorial-normalized Taylor coefficient in a single weighted derivative coordinate. -/
def weightedTaylorCoefficient (f : ℂ → V) (a : UEA) (z : ℂ) (n : ℕ) : B :=
  (n.factorial : ℂ)⁻¹ •
    iteratedDeriv n (weightedDerivative F G rho hsmooth hcalc hN hrho R L a ∘ f) z

end Langlands.Automorphic.GroupSchemeFunctions.UniformGrowthFrechetSpace

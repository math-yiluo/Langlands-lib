import Langlands.Representation.Archimedean.SmoothVectors
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! # Completed projective tensor products of Banach representations -/

noncomputable section

open Filter Set UniformSpace
open scoped TensorProduct ContDiff Manifold Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.CompletedProjectiveRepresentation

variable {ι : Type*} [Fintype ι]
  (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]

/-- The separated completion for the projective tensor seminorm. -/
abbrev Carrier := Completion (⨂[ℂ] i, E i)

/-- The continuous multilinear map of pure tensors into the completion. -/
def pure : ContinuousMultilinearMap ℂ E (Carrier E) :=
  Completion.toComplL.compContinuousMultilinearMap (PiTensorProduct.tprodL ℂ)

@[simp]
theorem pure_apply (v : ∀ i, E i) : pure E v = (PiTensorProduct.tprod ℂ v : Carrier E) := rfl

variable {E}

/-- The universal linear map into a Banach space, evaluated on the completion. -/
def lift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (B : ContinuousMultilinearMap ℂ E F) : Carrier E →L[ℂ] F :=
  (PiTensorProduct.liftIsometry ℂ E F B).fromCompletion

@[simp]
theorem lift_pure {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (B : ContinuousMultilinearMap ℂ E F) (v : ∀ i, E i) : lift B (pure E v) = B v := by
  simp [lift, PiTensorProduct.liftIsometry_apply_apply]

private theorem completion_opNorm_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (T : F →L[ℂ] F) : ‖T.completion‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  induction z using Completion.induction_on with
  | hp => exact isClosed_le T.completion.continuous.norm (continuous_const.mul continuous_norm)
  | ih x => simpa only [ContinuousLinearMap.completion_apply_coe, Completion.norm_coe] using T.le_opNorm x

variable {G : Type*} [Group G]
  (R : ∀ i, G →* (E i →L[ℂ] E i))

/-- The diagonal action on the completed projective tensor product. -/
def action : G →* (Carrier E →L[ℂ] Carrier E) where
  toFun g := (PiTensorProduct.mapL (fun i => R i g)).completion
  map_one' := by
    apply ContinuousLinearMap.ext
    exact congrFun (Completion.denseRange_coe.equalizer (ContinuousLinearMap.continuous _)
      (ContinuousLinearMap.continuous _) (funext fun x => by simp))
  map_mul' g h := by
    apply ContinuousLinearMap.ext
    exact congrFun (Completion.denseRange_coe.equalizer (ContinuousLinearMap.continuous _)
      (ContinuousLinearMap.continuous _) (funext fun x => by
        simp only [Function.comp_apply, ContinuousLinearMap.completion_apply_coe,
          mul_apply_eq_comp, map_mul]
        rw [PiTensorProduct.mapL_mul]
        rfl))

@[simp]
theorem action_pure (g : G) (v : ∀ i, E i) :
    action R g (pure E v) = pure E (fun i => R i g (v i)) := by
  simp [action, PiTensorProduct.mapL_apply, PiTensorProduct.map_tprod]

theorem norm_action_le (g : G) : ‖action R g‖ ≤ ∏ i, ‖R i g‖ :=
  (completion_opNorm_le _).trans (PiTensorProduct.opNorm_mapL _)

section Continuity

variable [TopologicalSpace G]

private theorem continuous_action_algebraic (hR : ∀ i, IsContinuousRepresentation (R i))
    (z : ⨂[ℂ] i, E i) : Continuous (fun g => action R g (z : Carrier E)) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    have hv : Continuous (fun g => pure E (fun i => R i g (v i))) :=
      (((pure E).restrictScalars ℝ).contDiff (n := ∞)).continuous.comp (continuous_pi fun i =>
        (hR i).comp (continuous_id.prodMk continuous_const))
    simp only [Completion.coe_smul, map_smul, ← pure_apply, action_pure]
    exact (continuous_const : Continuous (fun _ : G => c)).smul hv
  | add _ _ hf hg =>
    simp only [Completion.coe_add, map_add]
    exact hf.add hg

private theorem norm_action_bound_near [LocallyCompactSpace G] [∀ i, CompleteSpace (E i)]
    (hR : ∀ i, IsContinuousRepresentation (R i)) (g : G) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ y in 𝓝 g, ‖action R y‖ ≤ C := by
  obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
  have hbounded (i : ι) : ∃ c : ℝ, 1 ≤ c ∧ ∀ y ∈ K, ‖R i y‖ ≤ c := by
    let T : K → E i →L[ℂ] E i := fun y => R i y.val
    have hp (v : E i) : ∃ b : ℝ, ∀ y : K, ‖T y v‖ ≤ b := by
      have hv : Continuous (fun y => R i y v) := (hR i).comp (continuous_id.prodMk continuous_const)
      obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hv.continuousOn
      exact ⟨b, fun y => hb y.val y.property⟩
    obtain ⟨c, hc⟩ := banach_steinhaus (g := T) hp
    exact ⟨max 1 c, le_max_left _ _, fun y hy => (hc ⟨y, hy⟩).trans (le_max_right _ _)⟩
  choose C hC hbound using hbounded
  refine ⟨∏ i, C i, Finset.one_le_prod₀ (fun i _ => hC i), ?_⟩
  filter_upwards [hg] with y hy
  exact (norm_action_le R y).trans (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hbound i y hy))

/-- The completed action is jointly continuous for a finite family of jointly continuous
Banach actions of a locally compact group. -/
theorem isContinuous_action [LocallyCompactSpace G] [∀ i, CompleteSpace (E i)]
    (hR : ∀ i, IsContinuousRepresentation (R i)) : IsContinuousRepresentation (action R) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g, x⟩
  refine Metric.continuousAt_iff'.mpr (fun ε hε => ?_)
  obtain ⟨C, hC, hbound⟩ := norm_action_bound_near R hR g
  let δ := ε / (4 * C)
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδC : C * δ = ε / 4 := by
    dsimp [δ]
    field_simp
  obtain ⟨z, hz⟩ := (Completion.denseRange_coe : DenseRange ((↑) : (⨂[ℂ] i, E i) → Carrier E)).exists_dist_lt x hδ
  let q : Carrier E := z
  change dist x q < δ at hz
  have hfst : Tendsto Prod.fst (𝓝 (g, x)) (𝓝 g) := continuous_fst.continuousAt.tendsto
  have hbound' : ∀ᶠ y : G × Carrier E in 𝓝 (g, x), ‖action R y.1‖ ≤ C := hfst.eventually hbound
  have hNear : ∀ᶠ y : G × Carrier E in 𝓝 (g, x), dist y.2 x < δ :=
    Metric.continuousAt_iff'.mp (continuous_snd.continuousAt (x := (g, x))) δ hδ
  have hMiddle : ∀ᶠ y : G × Carrier E in 𝓝 (g, x),
      dist (action R y.1 q) (action R g q) < ε / 4 :=
    Metric.continuousAt_iff'.mp (((continuous_action_algebraic R hR z).comp continuous_fst :
      Continuous (fun y : G × Carrier E => action R y.1 q)).continuousAt (x := (g, x))) _
      (by positivity)
  filter_upwards [hbound', hNear, hMiddle] with y hy hxy hm
  have hgC := hbound.self_of_nhds
  have hTail : dist (action R g q) (action R g x) < ε / 4 := by
    refine ((action R g).dist_le_opNorm q x).trans_lt ?_
    rw [← hδC]
    exact (mul_le_mul_of_nonneg_right hgC dist_nonneg).trans_lt (mul_lt_mul_of_pos_left (by simpa only [dist_comm q x] using hz) hC₀)
  have hFirst : dist (action R y.1 y.2) (action R y.1 q) < ε / 2 := by
    refine ((action R y.1).dist_le_opNorm y.2 q).trans_lt ?_
    have hDist : dist y.2 q < δ + δ := by
      calc
        _ ≤ dist y.2 x + dist x q := dist_triangle _ _ _
        _ < δ + δ := add_lt_add hxy hz
    have h := (mul_le_mul_of_nonneg_right hy (dist_nonneg (x := y.2) (y := q))).trans_lt
      (mul_lt_mul_of_pos_left hDist hC₀)
    rw [mul_add, hδC] at h
    linarith
  exact (dist_triangle _ (action R y.1 q) _).trans_lt (by
    have ht := dist_triangle (action R y.1 q) (action R g q) (action R g x)
    linarith)

end Continuity

section Smoothness

variable {A H : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [TopologicalSpace H] [TopologicalSpace G] [ChartedSpace H G] (I : ModelWithCorners ℝ A H)

/-- Pure tensors of genuine smooth vectors have smooth diagonal orbits. -/
theorem isSmoothVector_pure (v : ∀ i, E i) (hv : ∀ i, IsSmoothVector I (R i) (v i)) :
    IsSmoothVector I (action R) (pure E v) := by
  have hP : ContMDiff 𝓘(ℝ, (∀ i, E i)) 𝓘(ℝ, Carrier E) ∞ (pure E) :=
    ((pure E).restrictScalars ℝ).contDiff.contMDiff
  have hV : ContMDiff I 𝓘(ℝ, (∀ i, E i)) ∞ (fun g => fun i => R i g (v i)) :=
    contMDiff_pi_module_iff.mpr hv
  change ContMDiff I 𝓘(ℝ, Carrier E) ∞ (fun g => action R g (pure E v))
  simp_rw [action_pure]
  exact hP.comp hV

end Smoothness

/-- Banach tensor products carry the actual completed diagonal action, with joint continuity
and preservation of genuine smooth pure tensors. -/
def CompletedProjectiveRepresentationStatement : Prop :=
  ∀ {A H G : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace H]
    [Group G] [TopologicalSpace G] [LocallyCompactSpace G] [ChartedSpace H G]
    (I : ModelWithCorners ℝ A H) {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (R : ∀ i, G →* (E i →L[ℂ] E i)),
    (∀ i, IsContinuousRepresentation (R i)) → IsContinuousRepresentation (action R) ∧
    ∀ v : ∀ i, E i, (∀ i, IsSmoothVector I (R i) (v i)) → IsSmoothVector I (action R) (pure E v)

theorem completedProjectiveRepresentation : CompletedProjectiveRepresentationStatement := by
  intro A H G _ _ _ _ _ _ _ I ι _ E _ _ _ R hR
  exact ⟨isContinuous_action R hR, isSmoothVector_pure R I⟩

end Langlands.Archimedean.CompletedProjectiveRepresentation

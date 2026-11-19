import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-! # Pointwise analytic germs on continuous functions on a compact space -/

noncomputable section

open Filter
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {𝕜 K E F ι : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace K] [CompactSpace K] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

omit [CompactSpace K] [Fintype ι] in
private theorem evaluate_update [DecidableEq ι] (u : ι → C(K, E)) (i : ι)
    (v : C(K, E)) (k : K) :
    (fun j => Function.update u i v j k) =
      Function.update (fun j => u j k) i (v k) := by
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h]

private def pointwiseMultilinear (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :
    MultilinearMap 𝕜 (fun _ : ι => C(K, E)) C(K, F) where
  toFun u :=
    ⟨fun k => m (fun i => u i k), m.cont.comp (continuous_pi fun i => (u i).continuous)⟩
  map_update_add' u i x y := by
    ext k
    change m (fun j => Function.update u i (x + y) j k) =
      m (fun j => Function.update u i x j k) + m (fun j => Function.update u i y j k)
    simp only [evaluate_update, ContinuousMap.add_apply, m.map_update_add]
  map_update_smul' u i c x := by
    ext k
    change m (fun j => Function.update u i (c • x) j k) =
      c • m (fun j => Function.update u i x j k)
    simp only [evaluate_update, ContinuousMap.smul_apply, m.map_update_smul]

private theorem norm_pointwiseMultilinear_le
    (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (u : ι → C(K, E)) :
    ‖pointwiseMultilinear m u‖ ≤ ‖m‖ * ∏ i, ‖u i‖ := by
  apply (ContinuousMap.norm_le (pointwiseMultilinear m u) (by positivity)).mpr
  intro k
  change ‖m (fun i => u i k)‖ ≤ ‖m‖ * ∏ i, ‖u i‖
  exact m.le_opNorm_mul_prod_of_le (fun i => (u i).norm_coe_le_norm k)

/-- Apply a continuous multilinear map pointwise to continuous functions on `K`. -/
def pointwiseContinuousMultilinear (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :
    ContinuousMultilinearMap 𝕜 (fun _ : ι => C(K, E)) C(K, F) :=
  (pointwiseMultilinear (K := K) m).mkContinuous ‖m‖
    (fun u => norm_pointwiseMultilinear_le m u)

@[simp]
theorem pointwiseContinuousMultilinear_apply
    (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (u : ι → C(K, E)) (k : K) :
    pointwiseContinuousMultilinear m u k = m (fun i => u i k) := rfl

theorem norm_pointwiseContinuousMultilinear_le
    (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :
    ‖pointwiseContinuousMultilinear (K := K) m‖ ≤ ‖m‖ :=
  (pointwiseMultilinear (K := K) m).mkContinuous_norm_le (norm_nonneg m)
    (fun u => norm_pointwiseMultilinear_le m u)

/-- An analytic germ at `x` acts pointwise as an analytic germ at the constant function
with value `x`, for the supremum norms on the continuous function spaces. -/
theorem exists_analyticAt_pointwise [CompleteSpace F] {f : E → F} {x : E}
    (hf : AnalyticAt 𝕜 f x) (K : Type*) [TopologicalSpace K] [CompactSpace K] :
    ∃ g : C(K, E) → C(K, F), AnalyticAt 𝕜 g (ContinuousMap.const K x) ∧
      ∀ᶠ u in 𝓝 (ContinuousMap.const K x), ∀ k : K, g u k = f (u k) := by
  obtain ⟨p, r, hp⟩ := hf
  let q : FormalMultilinearSeries 𝕜 C(K, E) C(K, F) := fun n =>
    pointwiseContinuousMultilinear (p n)
  let c : C(K, E) := ContinuousMap.const K x
  have hr : r ≤ q.radius := hp.r_le.trans
    (FormalMultilinearSeries.radius_le_of_le fun n => norm_pointwiseContinuousMultilinear_le (p n))
  let g : C(K, E) → C(K, F) := fun u => q.sum (u - c)
  have hg : HasFPowerSeriesOnBall g q c r := by
    refine ⟨hr, hp.r_pos, fun {y} hy => ?_⟩
    have hy' := Metric.mem_eball.mp hy
    have hyq : y ∈ Metric.eball (0 : C(K, E)) q.radius :=
      Metric.mem_eball.mpr (hy'.trans_le hr)
    simpa only [g, add_sub_cancel_left] using q.hasSum hyq
  refine ⟨g, hg.analyticAt, ?_⟩
  filter_upwards [Metric.eball_mem_nhds c hp.r_pos] with u hu k
  have hdist : edist (u k) (c k) ≤ edist u c := by
    simpa only [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] using
      (ContinuousMap.dist_apply_le_dist (f := u) (g := c) k)
  have huk : u k ∈ Metric.eball x r :=
    Metric.mem_eball.mpr (hdist.trans_lt (Metric.mem_eball.mp hu))
  have hqsum := (ContinuousMap.evalCLM (R := 𝕜) (M := F) k).hasSum (hg.hasSum_sub hu)
  exact hqsum.unique (by
    simpa only [q, ContinuousMap.evalCLM_apply, pointwiseContinuousMultilinear_apply,
      ContinuousMap.sub_apply, ContinuousMap.const_apply, c] using hp.hasSum_sub huk)

end Langlands.Analysis

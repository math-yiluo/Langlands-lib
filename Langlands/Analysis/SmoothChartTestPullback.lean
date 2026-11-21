import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! # Pullback of test functions along an open smooth chart -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Function Seminorm Set TopologicalSpace WithSeminorms
open scoped ContDiff Distributions Topology

namespace Langlands.Analysis

universe u v s

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {𝕜 : Type s} [RCLike 𝕜]

private def chartPullbackFun (e : OpenPartialHomeomorph E F) (f : F → 𝕜) : E → 𝕜 :=
  e.source.indicator (f ∘ e)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem chartPullbackFun_eq (e : OpenPartialHomeomorph E F) (f : F → 𝕜) :
    EqOn (chartPullbackFun e f) (f ∘ e) e.source :=
  fun _ hx => indicator_of_mem hx _

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem support_chartPullbackFun_subset (e : OpenPartialHomeomorph E F)
    {f : F → 𝕜} {K : Set F} (hf : support f ⊆ K) :
    support (chartPullbackFun e f) ⊆ e.symm '' K := by
  intro x hx
  have hs : x ∈ e.source := by
    by_contra h
    exact hx (indicator_of_notMem h _)
  have hs' : e x ∈ support f := by
    intro h
    exact hx ((chartPullbackFun_eq e f hs).trans h)
  exact ⟨e x, hf hs', e.left_inv hs⟩

private def chartPullbackCompact (e : OpenPartialHomeomorph E F)
    (K : Compacts F) (hK : (K : Set F) ⊆ e.target) : Compacts E :=
  ⟨e.symm '' (K : Set F), K.isCompact.image_of_continuousOn (e.symm.continuousOn.mono hK)⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
private theorem chartPullbackCompact_subset (e : OpenPartialHomeomorph E F)
    (K : Compacts F) (hK : (K : Set F) ⊆ e.target) :
    (chartPullbackCompact e K hK : Set E) ⊆ e.source := by
  rintro x ⟨y, hy, rfl⟩
  exact e.map_target (hK hy)

private theorem contDiff_chartPullbackFun (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) {f : F → 𝕜} (hf : ContDiff ℝ ∞ f)
    (K : Compacts F) (hK : (K : Set F) ⊆ e.target) (hfs : support f ⊆ K) :
    ContDiff ℝ ∞ (chartPullbackFun e f) := by
  let L := chartPullbackCompact e K hK
  have hs : support (chartPullbackFun e f) ⊆ (L : Set E) := support_chartPullbackFun_subset e hfs
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ e.source
  · have hd := hf.contDiffAt.comp x (he.contDiffAt (e.open_source.mem_nhds hx))
    apply hd.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hx] with y hy using chartPullbackFun_eq e f hy
  · have hxL : x ∉ (L : Set E) := fun h => hx (chartPullbackCompact_subset e K hK h)
    apply (contDiffAt_const (c := (0 : 𝕜))).congr_of_eventuallyEq
    filter_upwards [L.isCompact.isClosed.isOpen_compl.mem_nhds hxL] with y hy
    by_contra h
    exact hy (hs h)

private theorem exists_chartDerivativeBound (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (L : Compacts E) (hL : (L : Set E) ⊆ e.source) (i : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ x ∈ (L : Set E), ∀ j, 1 ≤ j → j ≤ i →
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ D ^ j := by
  have hb (j : Fin (i + 1)) :
      ∃ C : ℝ, ∀ x ∈ (L : Set E), ‖iteratedFDerivWithin ℝ (j : ℕ) e e.source x‖ ≤ C := by
    have hc := (he.continuousOn_iteratedFDerivWithin (m := (j : ℕ)) (by simp)
      e.open_source.uniqueDiffOn).norm
    obtain ⟨C, hC⟩ := L.isCompact.bddAbove_image (hc.mono hL)
    exact ⟨C, fun x hx => hC ⟨x, hx, rfl⟩⟩
  choose B hB using hb
  let D := 1 + ∑ j : Fin (i + 1), |B j|
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => abs_nonneg (B j))
  refine ⟨D, hD, fun x hx j hj hji => ?_⟩
  let k : Fin (i + 1) := ⟨j, Nat.lt_succ_of_le hji⟩
  calc
    ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ B k := hB k x hx
    _ ≤ |B k| := le_abs_self _
    _ ≤ ∑ l : Fin (i + 1), |B l| :=
      Finset.single_le_sum (f := fun l => |B l|) (fun l _ => abs_nonneg _) (Finset.mem_univ k)
    _ ≤ D := le_add_of_nonneg_left zero_le_one
    _ ≤ D ^ j := le_self_pow₀ hD (by omega)

private def fixedSupportChartPullback (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts F) (hK : (K : Set F) ⊆ e.target) :
    𝓓_{K}(F, 𝕜) →L[𝕜] 𝓓_{chartPullbackCompact e K hK}(E, 𝕜) := by
  let L := chartPullbackCompact e K hK
  let P : 𝓓_{K}(F, 𝕜) →ₗ[𝕜] 𝓓_{L}(E, 𝕜) :=
    { toFun := fun f => ContDiffMapSupportedIn.of_support_subset
        (contDiff_chartPullbackFun e he f.contDiff K hK f.support_subset)
        (support_chartPullbackFun_subset e f.support_subset)
      map_add' := fun f g => ContDiffMapSupportedIn.ext fun x => by
        by_cases hx : x ∈ e.source <;> simp [chartPullbackFun, hx]
      map_smul' := fun c f => ContDiffMapSupportedIn.ext fun x => by
        by_cases hx : x ∈ e.source <;> simp [chartPullbackFun, hx] }
  refine { toLinearMap := P, cont := ?_ }
  refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms 𝕜 F 𝕜 ⊤ K)
    (ContDiffMapSupportedIn.withSeminorms 𝕜 E 𝕜 ⊤ L) P (.of_real fun i => ?_)
  obtain ⟨D, hD, hDb⟩ := exists_chartDerivativeBound e he L (chartPullbackCompact_subset e K hK) i
  let C := (i.factorial : ℝ) * D ^ i
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hD) _)
  refine ⟨Finset.Iic i, C, fun f => ?_⟩
  let p := (Finset.Iic i).sup (fun j => ContDiffMapSupportedIn.seminorm 𝕜 F 𝕜 ⊤ K j)
  change ContDiffMapSupportedIn.seminorm 𝕜 E 𝕜 ⊤ L i (P f) ≤ C * p f
  refine (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜 (mul_nonneg hC (apply_nonneg _ _))
    i (P f)).mpr ?_
  intro x hx
  have hx' := chartPullbackCompact_subset e K hK hx
  have hder (j : ℕ) (hj : j ≤ i) :
      ‖iteratedFDerivWithin ℝ j f univ (e x)‖ ≤ p f := by
    rw [iteratedFDerivWithin_univ]
    exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜).trans
      (Finset.le_sup (f := fun k => ContDiffMapSupportedIn.seminorm 𝕜 F 𝕜 ⊤ K k)
        (Finset.mem_Iic.mpr hj) f)
  have h := norm_iteratedFDerivWithin_comp_le (n := i) f.contDiff.contDiffOn he
    (by simp) uniqueDiffOn_univ e.open_source.uniqueDiffOn (mapsTo_univ _ _) hx'
    hder (hDb x hx)
  rw [← iteratedFDerivWithin_of_isOpen i e.open_source hx']
  have hEq : EqOn (fun x => P f x) ((f : F → 𝕜) ∘ e) e.source :=
    chartPullbackFun_eq e f
  rw [iteratedFDerivWithin_congr hEq hx' i]
  exact h.trans_eq (by dsimp only [C]; ring)

/-- Pull back tests on the target of a smooth open partial homeomorphism
by composition on the source and extension by zero. -/
def smoothChartTestPullback (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) :
    𝓓(⟨e.target, e.open_target⟩, 𝕜) →L[𝕜] 𝓓(⟨e.source, e.open_source⟩, 𝕜) := by
  let P (f : 𝓓(⟨e.target, e.open_target⟩, 𝕜)) :
      𝓓(⟨e.source, e.open_source⟩, 𝕜) := by
    let K : Compacts F := ⟨tsupport f, f.hasCompactSupport⟩
    have hK : (K : Set F) ⊆ e.target := f.tsupport_subset
    let L := chartPullbackCompact e K hK
    have hs : tsupport (chartPullbackFun e f) ⊆ (L : Set E) :=
      closure_minimal (support_chartPullbackFun_subset e (subset_tsupport f)) L.isCompact.isClosed
    exact ⟨chartPullbackFun e f,
      contDiff_chartPullbackFun e he f.contDiff K hK (subset_tsupport f),
      L.isCompact.of_isClosed_subset isClosed_closure hs, hs.trans (chartPullbackCompact_subset e K hK)⟩
  exact TestFunction.limitCLM 𝕜 P
    (fun K hK => (TestFunction.ofSupportedInCLM 𝕜 (chartPullbackCompact_subset e K hK)).comp
      (fixedSupportChartPullback e he K hK)) (fun _ _ _ => TestFunction.ext fun _ => rfl)

theorem smoothChartTestPullback_apply (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (f : 𝓓(⟨e.target, e.open_target⟩, 𝕜))
    {x : E} (hx : x ∈ e.source) :
    smoothChartTestPullback e he f x = f (e x) :=
  chartPullbackFun_eq e f hx

theorem smoothChartTestPullback_apply_of_notMem (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (f : 𝓓(⟨e.target, e.open_target⟩, 𝕜))
    {x : E} (hx : x ∉ e.source) :
    smoothChartTestPullback e he f x = 0 :=
  indicator_of_notMem hx _

/-- Pullback carries the topological support into the inverse image
under the inverse chart, viewed as an image of the compact support. -/
theorem tsupport_smoothChartTestPullback_subset (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (f : 𝓓(⟨e.target, e.open_target⟩, 𝕜)) :
    tsupport (smoothChartTestPullback e he f) ⊆ e.symm '' tsupport f :=
  closure_minimal (support_chartPullbackFun_subset e (subset_tsupport f))
    (f.hasCompactSupport.image_of_continuousOn
      (e.symm.continuousOn.mono f.tsupport_subset)).isClosed

/-- The chain rule holds throughout the source of the chart. -/
theorem fderiv_smoothChartTestPullback (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (f : 𝓓(⟨e.target, e.open_target⟩, 𝕜))
    {x : E} (hx : x ∈ e.source) :
    fderiv ℝ (smoothChartTestPullback e he f : E → 𝕜) x =
      (fderiv ℝ f (e x)).comp (fderiv ℝ e x) := by
  have hEq : (smoothChartTestPullback e he f : E → 𝕜) =ᶠ[𝓝 x] (f : F → 𝕜) ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
      using smoothChartTestPullback_apply e he f hy
  rw [hEq.fderiv_eq]
  exact fderiv_comp x (f.contDiff.differentiable (by simp) (e x))
    ((he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp))

theorem smoothChartTestPullback_symm_apply (e : OpenPartialHomeomorph E F)
    (he : ContDiffOn ℝ ∞ e e.source) (hs : ContDiffOn ℝ ∞ e.symm e.target)
    (f : 𝓓(⟨e.target, e.open_target⟩, 𝕜)) :
    smoothChartTestPullback e.symm hs (smoothChartTestPullback e he f) = f := by
  ext x
  by_cases hx : x ∈ e.target
  · rw [smoothChartTestPullback_apply e.symm hs _ hx,
      smoothChartTestPullback_apply e he _ (e.map_target hx), e.right_inv hx]
  · rw [smoothChartTestPullback_apply_of_notMem e.symm hs _ hx]
    exact (image_eq_zero_of_notMem_tsupport (fun hf => hx (f.tsupport_subset hf))).symm

end Langlands.Analysis

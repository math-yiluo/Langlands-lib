import Langlands.Analysis.CompactParameterSmoothness
import Langlands.Analysis.SmoothIntervalParameterIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Distribution.TestFunction

/-! # Jointly smooth families with fixed compact test support -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

variable {P E F : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Bundle a jointly smooth parameter family whose tests have a common compact support. -/
def compactTestFamily {K : Compacts E} {s : Set P} {h : P × E → F}
    (hh : ContDiff ℝ ∞ h) (hs : ∀ t ∈ s, ∀ x ∉ K, h (t, x) = 0) (t : s) :
    𝓓_{K}(E, F) where
  toFun x := h (t.val, x)
  contDiff' := hh.comp (contDiff_const.prodMk contDiff_id)
  zero_on_compl' x hx := hs t.val t.property x hx

@[simp]
theorem compactTestFamily_apply {K : Compacts E} {s : Set P} {h : P × E → F}
    (hh : ContDiff ℝ ∞ h) (hs : ∀ t ∈ s, ∀ x ∉ K, h (t, x) = 0) (t : s) (x : E) :
    compactTestFamily hh hs t x = h (t.val, x) := rfl

private theorem iteratedFDeriv_slice {h : P × E → F} (hh : ContDiff ℝ ∞ h)
    (t : P) (x : E) (i : ℕ) :
    iteratedFDeriv ℝ i (fun y => h (t, y)) x =
      (iteratedFDeriv ℝ i h (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ P E) := by
  let L := ContinuousLinearMap.inr ℝ P E
  let H : P × E → F := fun z => h ((t, 0) + z)
  have hH : ContDiff ℝ ∞ H := hh.comp (contDiff_const.add contDiff_id)
  have heq : (fun y => h (t, y)) = H ∘ L := by
    funext y
    change h (t, y) = h (t + 0, 0 + y)
    simp
  rw [heq, L.iteratedFDeriv_comp_right hH x (by simp)]
  change (iteratedFDeriv ℝ i (fun z : P × E => h ((t, 0) + z)) (0, x)).compContinuousLinearMap
    (fun _ => L) = _
  rw [iteratedFDeriv_comp_add_left]
  simp [L]

/-- Joint smoothness and a common compact support give continuity in the smooth
fixed-support test topology. -/
theorem continuous_compactTestFamily {K : Compacts E} {s : Set P} {h : P × E → F}
    (hh : ContDiff ℝ ∞ h) (hs : ∀ t ∈ s, ∀ x ∉ K, h (t, x) = 0) :
    Continuous (compactTestFamily hh hs) := by
  apply (ContDiffMapSupportedIn.continuous_iff_comp _).mpr
  intro i
  let B := ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (K := K) (F := F) i
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ) (F := F)
    (fun _ : Fin i => ContinuousLinearMap.inr ℝ P E)
  let g : P × E → E [×i]→L[ℝ] F := L ∘ iteratedFDeriv ℝ i h
  have hg : Continuous g := L.continuous.comp (hh.continuous_iteratedFDeriv (by simp))
  have heq (t : s) (x : E) : B (compactTestFamily hh hs t) x = g (t.val, x) := by
    change ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (compactTestFamily hh hs t) x = _
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact iteratedFDeriv_slice hh t.val x i
  have : CompactSpace K := isCompact_iff_compactSpace.mp K.isCompact
  let A (t : s) : C(K, E [×i]→L[ℝ] F) :=
    ⟨fun x => g (t.val, x.val), hg.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hA : Continuous A := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hg.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  have hout (t : s) {x : E} (hx : x ∉ K) : B (compactTestFamily hh hs t) x = 0 := by
    change ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (compactTestFamily hh hs t) x = 0
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact Function.notMem_support.mp fun h =>
      hx ((compactTestFamily hh hs t).tsupport_subset (support_iteratedFDeriv_subset i h))
  refine continuous_iff_continuousAt.mpr fun t => Metric.continuousAt_iff'.mpr fun ε hε => ?_
  have hlim : ∀ᶠ u in 𝓝 t, dist (A u) (A t) < ε :=
    (Metric.continuousAt_iff' (f := A)).mp hA.continuousAt ε hε
  filter_upwards [hlim] with u hu
  change dist (B (compactTestFamily hh hs u)) (B (compactTestFamily hh hs t)) < ε
  refine lt_of_le_of_lt ?_ hu
  apply (BoundedContinuousFunction.dist_le (dist_nonneg : 0 ≤ dist (A u) (A t))).mpr
  intro x
  by_cases hx : x ∈ K
  · rw [heq, heq]
    exact ContinuousMap.dist_apply_le_dist (f := A u) (g := A t) ⟨x, hx⟩
  · rw [hout u hx, hout t hx, dist_self]
    exact dist_nonneg

/-- Integrate the time derivative over the rescaled unit interval. For complete
`F`, this extends the time divided difference smoothly through time zero. -/
def smoothTimeDifferenceQuotient (h : ℝ × E → F) (p : ℝ × E) : F :=
  ∫ u in (0 : ℝ)..1, fderiv ℝ h (p.1 * u, p.2) (1, 0)

theorem contDiff_smoothTimeDifferenceQuotient {h : ℝ × E → F} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (smoothTimeDifferenceQuotient h) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ h) := hh.fderiv_right (by simp)
  have h_eval : ContDiff ℝ ∞ (fun z : ℝ × E => fderiv ℝ h z (1, 0)) :=
    hD.clm_apply contDiff_const
  have hg : ContDiff ℝ ∞ (fun p : (ℝ × E) × ℝ => fderiv ℝ h (p.1.1 * p.2, p.1.2) (1, 0)) :=
    h_eval.comp (by fun_prop)
  exact Langlands.Analysis.contDiff_intervalIntegral_of_joint hg zero_le_one

private theorem deriv_timeSlice {h : ℝ × E → F} (hh : ContDiff ℝ ∞ h) (t : ℝ) (x : E) :
    deriv (fun u => h (u, x)) t = fderiv ℝ h (t, x) (1, 0) := by
  have hd := (hh.differentiable (by simp) (t, x)).hasFDerivAt
  have hc : HasDerivAt (fun u : ℝ => (u, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (hd.comp_hasDerivAt t hc).deriv

variable [CompleteSpace F]

@[simp]
theorem smoothTimeDifferenceQuotient_zero (h : ℝ × E → F) (x : E) :
    smoothTimeDifferenceQuotient h (0, x) = fderiv ℝ h (0, x) (1, 0) := by
  simp [smoothTimeDifferenceQuotient]

theorem smul_smoothTimeDifferenceQuotient {h : ℝ × E → F} (hh : ContDiff ℝ ∞ h)
    (t : ℝ) (x : E) :
    t • smoothTimeDifferenceQuotient h (t, x) = h (t, x) - h (0, x) := by
  let g : ℝ → F := fun u => h (u, x)
  have hg : ContDiff ℝ ∞ g := hh.comp (contDiff_id.prodMk contDiff_const)
  have hderiv : (fun u => fderiv ℝ h (u, x) (1, 0)) = deriv g :=
    funext fun u => (deriv_timeSlice hh u x).symm
  have hscale : t • smoothTimeDifferenceQuotient h (t, x) =
      ∫ u in (0 : ℝ)..t, fderiv ℝ h (u, x) (1, 0) := by
    simpa only [smoothTimeDifferenceQuotient, mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
        (fun u => fderiv ℝ h (u, x) (1, 0)) t
  rw [hscale, hderiv]
  exact intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hg.of_le (by simp)).contDiffOn

end Langlands.HarmonicAnalysis

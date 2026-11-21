import Langlands.HarmonicAnalysis.Distribution.ProductJetTransform
import Langlands.HarmonicAnalysis.Distribution.SmoothTestParameters
import Langlands.HarmonicAnalysis.Distribution.SmoothJetSlotNilpotence
import Langlands.Analysis.MixedParameterDerivatives

/-! # The leading full jet of a vector-field derivative -/

noncomputable section

open Set Filter TopologicalSpace
open scoped Classical ContDiff Distributions Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

open Langlands.Analysis (fderiv_fst_slice_apply)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def evalCompactJet {S : Compacts E} (k : ℕ) (x : E) (v : Fin k → E) :
    𝓓_{S}(E, ℂ) →L[ℝ] ℂ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ v).comp
    ((BoundedContinuousFunction.evalCLM ℝ x).comp (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k))

@[simp] private theorem evalCompactJet_apply {S : Compacts E} (k : ℕ) (x : E) (v : Fin k → E)
    (f : 𝓓_{S}(E, ℂ)) : evalCompactJet k x v f = iteratedFDeriv ℝ k f x v := by
  change ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k f x v = _
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]

private theorem smoothTimeDifferenceQuotient_support_univ {S : Compacts E} {h : ℝ × E → ℂ}
    (hh : ContDiff ℝ ∞ h) (hs : ∀ t : ℝ, ∀ y ∉ S, h (t, y) = 0) {t : ℝ} {y : E} (hy : y ∉ S) :
    smoothTimeDifferenceQuotient h (t, y) = 0 := by
  by_cases ht : t = 0
  · subst t
    rw [smoothTimeDifferenceQuotient_zero, ← fderiv_fst_slice_apply (hh.differentiable (by simp) (0, y)),
      show (fun t : ℝ => h (t, y)) = 0 from funext fun t => hs t y hy,
      fderiv_zero]
    simp
  · have he := smul_smoothTimeDifferenceQuotient hh t y
    rw [hs t y hy, hs 0 y hy, sub_self] at he
    exact (smul_eq_zero.mp he).resolve_left ht

/-- Evaluation of a fixed spatial jet commutes with the time derivative of a
jointly smooth family with common compact test support. -/
theorem hasDerivAt_evalCompactJet_of_smoothFamily {S : Compacts E} {h : ℝ × E → ℂ}
    (hh : ContDiff ℝ ∞ h) (hS : ∀ t : ℝ, ∀ y ∉ S, h (t, y) = 0) (k : ℕ) (x : E) (v : Fin k → E) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k (fun y => h (t, y)) x v)
      (iteratedFDeriv ℝ k (fun y => fderiv ℝ h (0, y) (1, 0)) x v) 0 := by
  let inc (t : ℝ) : (univ : Set ℝ) := ⟨t, mem_univ t⟩
  let H (t : ℝ) : 𝓓_{S}(E, ℂ) := compactTestFamily hh (fun s _ y hy => hS s y hy) (inc t)
  let Q (t : ℝ) : 𝓓_{S}(E, ℂ) := compactTestFamily (contDiff_smoothTimeDifferenceQuotient hh)
    (fun _ _ _ hy => smoothTimeDifferenceQuotient_support_univ hh hS hy) (inc t)
  have hQc : Continuous Q := (continuous_compactTestFamily _ _).comp (continuous_id.subtype_mk _)
  let J := evalCompactJet (S := S) k x v
  have hQ (t : ℝ) : t • Q t = H t - H 0 := by
    ext y
    exact smul_smoothTimeDifferenceQuotient hh t y
  have hD : HasDerivAt (fun t => J (H t)) (J (Q 0)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have he : (fun t : ℝ => J (Q t)) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun t : ℝ => t⁻¹ • (J (H (0 + t)) - J (H 0))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := mem_compl_singleton_iff.mp ht
      rw [zero_add, ← map_sub, ← hQ t, map_smul, inv_smul_smul₀ ht0]
    exact ((J.continuous.comp hQc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he
  have hH (t : ℝ) : J (H t) = iteratedFDeriv ℝ k (fun y => h (t, y)) x v := evalCompactJet_apply k x v _
  have hQ0 : (Q 0 : E → ℂ) = fun y => fderiv ℝ h (0, y) (1, 0) :=
    funext fun y => smoothTimeDifferenceQuotient_zero h y
  simpa only [hH, show J (Q 0) = iteratedFDeriv ℝ k (fun y => fderiv ℝ h (0, y) (1, 0)) x v by
    rw [show J (Q 0) = iteratedFDeriv ℝ k (Q 0 : E → ℂ) x v from evalCompactJet_apply k x v _, hQ0]] using hD

/-- A field vanishing at the base point acts on the first potentially nonzero
jet by inserting its linearization in each slot. -/
def SmoothVectorFieldJetStatement : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℂ) (V : E → E) (x : E) (k : ℕ),
    ContDiff ℝ ∞ f → ContDiff ℝ ∞ V → V x = 0 →
    (∀ j < k, iteratedFDeriv ℝ j f x = 0) →
      iteratedFDeriv ℝ k (fun y => fderiv ℝ f y (V y)) x =
        jetSlotAction (fderiv ℝ V x) k (iteratedFDeriv ℝ k f x)

set_option maxHeartbeats 900000 in
theorem smoothVectorFieldJet : SmoothVectorFieldJetStatement := by
  intro E _ _ _ f V x k hf hV hV0 hLower
  let χ : ContDiffBump x := ⟨1, 2, by norm_num, by norm_num⟩
  let S : Compacts E := ⟨tsupport (χ : E → ℝ), χ.hasCompactSupport⟩
  let g (q : ℝ × E) := q.2 + q.1 • V q.2
  let h (q : ℝ × E) := χ q.2 • f (g q)
  have hg : ContDiff ℝ ∞ g := contDiff_snd.add (contDiff_fst.smul (hV.comp contDiff_snd))
  have hh : ContDiff ℝ ∞ h := (χ.contDiff.comp contDiff_snd).smul (hf.comp hg)
  have hS (t : ℝ) (y : E) (hy : y ∉ S) : h (t, y) = 0 := by
    have hχ : χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    change χ y • f (g (t, y)) = 0
    rw [hχ, zero_smul]
  have hχ : (χ : E → ℝ) =ᶠ[𝓝 x] 1 := χ.eventuallyEq_one
  apply ContinuousMultilinearMap.ext
  intro v
  have hD := hasDerivAt_evalCompactJet_of_smoothFamily hh hS k x v
  have hTime (y : E) : fderiv ℝ h (0, y) (1, 0) = χ y • fderiv ℝ f y (V y) := by
    rw [← fderiv_fst_slice_apply (hh.differentiable (by simp) (0, y)) 1, fderiv_apply_one_eq_deriv]
    have hPath : HasDerivAt (fun t : ℝ => y + t • V y) (V y) 0 := by
      simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (V y)).const_add y
    have hd := (((hf.differentiable (by simp) y).hasFDerivAt.comp_hasDerivAt_of_eq 0 hPath (by simp)).const_smul (χ y)).deriv
    exact hd
  have hTimeEq : (fun y => fderiv ℝ h (0, y) (1, 0)) =ᶠ[𝓝 x] (fun y => fderiv ℝ f y (V y)) := by
    filter_upwards [hχ] with y hy
    rw [hTime, show χ y = 1 from hy, one_smul]
  rw [(hTimeEq.iteratedFDeriv ℝ k).eq_of_nhds] at hD
  let A := fderiv ℝ V x
  let M := iteratedFDeriv ℝ k f x
  have hValue (t : ℝ) :
      iteratedFDeriv ℝ k (fun y => h (t, y)) x v = M (fun i => v i + t • A (v i)) := by
    have he : (fun y => h (t, y)) =ᶠ[𝓝 x] f ∘ (fun y => y + t • V y) := by
      filter_upwards [hχ] with y hy
      change χ y • f (y + t • V y) = f (y + t • V y)
      rw [show χ y = 1 from hy, one_smul]
    rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
    let P (y : E) := y + t • V y
    have hP : ContDiff ℝ ∞ P := contDiff_id.add (hV.const_smul t)
    have hPx : P x = x := by simp [P, hV0]
    have hDP : fderiv ℝ P x = ContinuousLinearMap.id ℝ E + t • A :=
      ((hasFDerivAt_id x).add ((hV.differentiable (by simp) x).hasFDerivAt.const_smul t)).fderiv
    change iteratedFDeriv ℝ k (f ∘ P) x v = _
    rw [iteratedFDeriv_comp_of_lower_eq_zero hf.contDiffAt hP.contDiffAt k
      (fun j hj => hPx.symm ▸ hLower j hj), hPx, hDP]
    rfl
  simp_rw [hValue] at hD
  have hLine : HasDerivAt (fun t : ℝ => fun i : Fin k => v i + t • A (v i)) (fun i => A (v i)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (A (v i))).const_add (v i)
  have hM := M.hasFDerivAt (x := v)
  have hExpected := hM.comp_hasDerivAt_of_eq 0 hLine (by ext i; simp)
  have hEq := hD.unique hExpected
  rw [hEq, ContinuousMultilinearMap.linearDeriv_apply, jetSlotAction_apply]

end Langlands.HarmonicAnalysis

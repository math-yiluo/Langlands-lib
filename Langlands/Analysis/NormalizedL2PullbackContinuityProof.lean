import Langlands.Analysis.NormalizedL2PullbackContinuityStatement

/-! # Joint continuity of normalized L² pullback -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Topology

namespace Langlands.NormalizedL2Pullback

universe uX uY uZ

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

private theorem map_refl_smul (c : ℝ≥0) :
    (c • ν).map (MeasurableEquiv.refl Y) = c • ν := by
  change (c • ν).map id = c • ν
  exact Measure.map_id

private theorem comp_normalized_identity (e : X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : μ.map e = c • ν) (f : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving e ⟨e.measurable, hmap⟩
      (isometryEquiv (μ := c • ν) (ν := ν) (MeasurableEquiv.refl Y) c hc
        (map_refl_smul c) f) =
      isometryEquiv e c hc hmap f := by
  let J := isometryEquiv (μ := c • ν) (ν := ν)
    (MeasurableEquiv.refl Y) c hc (map_refl_smul c)
  have hmp : MeasurePreserving e μ (c • ν) := ⟨e.measurable, hmap⟩
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (J f) hmp,
    hmp.quasiMeasurePreserving.ae_eq_comp
      (coeFn_isometryEquiv (μ := c • ν) (ν := ν)
        (MeasurableEquiv.refl Y) c hc (map_refl_smul c) f),
    coeFn_isometryEquiv e c hc hmap f] with x h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

private theorem isometryEquiv_scaling_congr (e : X ≃ᵐ Y) (c d : ℝ≥0)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hmapc : μ.map e = c • ν) (hmapd : μ.map e = d • ν)
    (hcd : c = d) (f : Lp ℂ 2 ν) :
    isometryEquiv e c hc hmapc f = isometryEquiv e d hd hmapd f := by
  subst d
  rfl

variable [TopologicalSpace X] [BorelSpace X] [R1Space X]
  [TopologicalSpace Y] [BorelSpace Y] [R1Space Y]
  [TopologicalSpace Z]
  [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure ν]

private theorem continuous_fixed_scaling
    (e : Z → X ≃ᵐ Y) (c : ℝ≥0) (hc : c ≠ 0)
    (hmap : ∀ z, μ.map (e z) = c • ν)
    (he : Continuous (fun zx : Z × X => e zx.1 zx.2)) :
    Continuous (fun zf : Z × Lp ℂ 2 ν =>
      isometryEquiv (e zf.1) c hc (hmap zf.1) zf.2) := by
  let J : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 (c • ν) :=
    isometryEquiv (MeasurableEquiv.refl Y) c hc (map_refl_smul c)
  let g : C(Z, C(X, Y)) := (⟨_, he⟩ : C(Z × X, Y)).curry
  have hmp (z : Z) : MeasurePreserving (g z) μ (c • ν) :=
    ⟨(e z).measurable, hmap z⟩
  have hcont := (J.continuous.comp continuous_snd).compMeasurePreservingLp
    (g.continuous.comp continuous_fst) (fun zf => hmp zf.1) (by simp)
  convert hcont using 1
  funext zf
  exact (comp_normalized_identity (e zf.1) c hc (hmap zf.1) zf.2).symm

/-- Joint continuity of the published normalized pullback under a locally
constant nonzero pushforward factor. -/
theorem locallyConstantScalingContinuity :
    LocallyConstantScalingContinuity.{uX,uY,uZ} := by
  intro X Y Z tX mX bX rX tY mY bY rY tZ μ ν hμ hν e c hc hmap he hcloc
  apply continuous_iff_continuousAt.mpr
  intro zf
  let s : Set (Z × Lp ℂ 2 ν) := {q | c q.1 = c zf.1}
  have hs : IsOpen s := (hcloc.isOpen_fiber (c zf.1)).preimage continuous_fst
  let e' : s → X ≃ᵐ Y := fun q => e q.val.1
  have hm (q : s) : μ.map (e' q) = c zf.1 • ν := by
    change μ.map (e q.val.1) = c zf.1 • ν
    rw [hmap q.val.1, q.property]
  have he' : Continuous (fun qx : s × X => e' qx.1 qx.2) :=
    he.comp ((continuous_fst.comp
      (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd)
  have H := continuous_fixed_scaling e' (c zf.1) (hc zf.1) hm he'
  have hrestrict : Continuous (fun q : s =>
      isometryEquiv (e q.val.1) (c q.val.1) (hc q.val.1)
        (hmap q.val.1) q.val.2) := by
    have h := H.comp
      (continuous_id.prodMk (continuous_snd.comp continuous_subtype_val))
    convert h using 1
    funext q
    exact isometryEquiv_scaling_congr (e q.val.1) (c q.val.1) (c zf.1)
      (hc q.val.1) (hc zf.1) (hmap q.val.1) (hm q) q.property q.val.2
  exact (hs.isOpenEmbedding_subtypeVal.continuousAt_iff
    (x := (⟨zf, rfl⟩ : s))).mp hrestrict.continuousAt

end Langlands.NormalizedL2Pullback

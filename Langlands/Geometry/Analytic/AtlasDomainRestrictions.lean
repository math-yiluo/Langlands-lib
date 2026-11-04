import Langlands.Geometry.Analytic.AtlasDomainChartCoherence

/-! # Actual bounded restrictions between arbitrary local full affinoid domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

theorem domainSubset_chart (i j : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    a.chart i '' U.locus ⊆ Set.range (a.chart j) := by
  intro x hx
  obtain ⟨y, _, hy⟩ := h hx
  exact ⟨y, hy⟩

/-- Actual inclusion after reexpressing the source domain over the target's
original chart. Full representation constructs its bounded restriction. -/
def domainInChartInclusionOfSubset (i j : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    a.domainInChart i j U (a.domainSubset_chart i j U V h) ⟶ V :=
  Domain.inclusionOfSubset _ V (by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := h hx
    exact (a.isEmbedding_chart j).injective hyx ▸ hy)

/-- Every ambient containment of local full domains constructs an actual
bounded restriction, without a common original upper chart. -/
def domainRestriction (i j : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    BoundedAlgHom K V.algebra U.algebra :=
  (a.domainInChartInclusionOfSubset i j U V h).restriction

theorem domainRestriction_comp_baseMap (i j : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    (a.domainRestriction i j U V h).comp V.baseMap =
      a.domainChartRestriction i j U (a.domainSubset_chart i j U V h) :=
  (a.domainInChartInclusionOfSubset i j U V h).comp_baseMap

/-- One actual bounded structural equation determines every competing map. -/
theorem eq_domainRestriction_of_over_base (i j : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus)
    (f : BoundedAlgHom K V.algebra U.algebra)
    (hf : f.comp V.baseMap =
      a.domainChartRestriction i j U (a.domainSubset_chart i j U V h)) :
    f = a.domainRestriction i j U V h :=
  V.represents.hom_ext U.algebra f _ (hf.trans (a.domainRestriction_comp_baseMap i j U V h).symm)

theorem domainRestriction_chart (i j : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus)
    (x : BanachSpectrum U.algebra) :
    a.chart j (V.spectrumMap
        (BanachSpectrum.comap (a.domainRestriction i j U V h).toBoundedRingHom x)) =
      a.chart i (U.spectrumMap x) := by
  have heq :
      V.spectrumMap (BanachSpectrum.comap
          (a.domainRestriction i j U V h).toBoundedRingHom x) =
        BanachSpectrum.comap
          (a.domainChartRestriction i j U (a.domainSubset_chart i j U V h)).toBoundedRingHom x := by
    apply BanachSpectrum.ext
    intro b
    exact congrArg (fun f : BoundedAlgHom K (a.algebra j) U.algebra => x (f b))
      (a.domainRestriction_comp_baseMap i j U V h)
  exact (congrArg (a.chart j) heq).trans
    (a.domainChartRestriction_chart i j U (a.domainSubset_chart i j U V h) x)

/-- Composing with any original chart containing the target domain's image
recovers the source's direct structural map from that chart. -/
theorem domainRestriction_comp_chart (i j k : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus)
    (hV : a.chart j '' V.locus ⊆ Set.range (a.chart k))
    (hU : a.chart i '' U.locus ⊆ Set.range (a.chart k)) :
    (a.domainRestriction i j U V h).comp (a.domainChartRestriction j k V hV) =
      a.domainChartRestriction i k U hU := by
  let hj := a.domainSubset_chart i j U V h
  have hUk : a.chart j '' (a.domainInChart i j U hj).locus ⊆ Set.range (a.chart k) := by
    rw [a.chart_image_domainInChart i j U hj]
    exact hU
  have hnat := a.domainChartRestriction_naturality j k
    (a.domainInChartInclusionOfSubset i j U V h) hV hUk
  exact hnat.trans (a.domainChartRestriction_reexpression i j k U hj hU hUk)

/-- Actual bounded restrictions compose across any three original local-domain
presentations. Full-test uniqueness identifies the entire algebra maps. -/
theorem domainRestriction_comp (i j k : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (W : Domain K (a.algebra k))
    (hUV : a.chart i '' U.locus ⊆ a.chart j '' V.locus)
    (hVW : a.chart j '' V.locus ⊆ a.chart k '' W.locus)
    (hUW : a.chart i '' U.locus ⊆ a.chart k '' W.locus) :
    (a.domainRestriction i j U V hUV).comp (a.domainRestriction j k V W hVW) =
      a.domainRestriction i k U W hUW := by
  apply a.eq_domainRestriction_of_over_base i k U W hUW
  have h₁ := congrArg (fun f : BoundedAlgHom K (a.algebra k) V.algebra =>
    (a.domainRestriction i j U V hUV).comp f)
    (a.domainRestriction_comp_baseMap j k V W hVW)
  exact h₁.trans (a.domainRestriction_comp_chart i j k U V hUV
    (a.domainSubset_chart j k V W hVW) (a.domainSubset_chart i k U W hUW))

/-- Same-chart actual inclusions are recovered with their original bounded maps. -/
theorem domainRestriction_sameChart (i : a.Index)
    {U V : Domain K (a.algebra i)} (f : U ⟶ V) :
    a.domainRestriction i i U V (Set.image_mono f.subset) = f.restriction := by
  symm
  apply a.eq_domainRestriction_of_over_base i i U V (Set.image_mono f.subset)
  exact f.comp_baseMap.trans
    (a.domainChartRestriction_self i U
      (a.domainSubset_chart i i U V (Set.image_mono f.subset))).symm

@[simp]
theorem domainRestriction_id (i : a.Index) (U : Domain K (a.algebra i)) :
    a.domainRestriction i i U U Subset.rfl = BoundedAlgHom.id K U.algebra :=
  a.domainRestriction_sameChart i (𝟙 U)

/-- The restriction itself fully represents the literal relative ambient
subset inside the target domain's actual spectrum. -/
theorem domainRestriction_represents (i j : a.Index)
    (U : Domain K (a.algebra i)) (V : Domain K (a.algebra j))
    (h : a.chart i '' U.locus ⊆ a.chart j '' V.locus) :
    Represents K (a.domainRestriction i j U V h)
      ((fun x : BanachSpectrum V.algebra => a.chart j (V.spectrumMap x)) ⁻¹'
        (a.chart i '' U.locus)) := by
  let W := a.domainInChart i j U (a.domainSubset_chart i j U V h)
  let f := a.domainInChartInclusionOfSubset i j U V h
  have hrep : Represents K (a.domainRestriction i j U V h) (V.relative W f).locus :=
    (V.relative W f).represents
  rw [V.relative_locus_eq_preimage_of_injective V.spectrumMap_injective] at hrep
  exact hrep

end Langlands.Analytic.IndexedAffinoidAtlas

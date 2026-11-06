import Langlands.Geometry.Analytic.RecognizedAtlasExtension
import Langlands.Geometry.Analytic.AtlasDomainTensorIntersection

/-! # Canonical full original-chart restrictions through nested recognition -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- An original chart, first recognized and then retained as its actual
whole local-domain presentation in the recognition atlas. -/
def recognitionOriginalLocalDomain (s : a.Index) : LocalDomain a.recognitionAtlas :=
  a.recognitionAtlas.originalLocalDomain (a.originalRecognitionIndex s)

theorem recognitionOriginalLocalDomain_locus (s : a.Index) :
    (a.recognitionOriginalLocalDomain s).locus = Set.range (a.chart s) :=
  (a.recognitionAtlas.originalLocalDomain_locus _).trans
    (a.recognitionAtlas_original_range s)

/-- The unchanged original chart algebra fully represents its actual
domain in the constructed recognized presentation. -/
def recognitionOriginalDomain (s : a.Index) :
    Domain K (a.recognitionOriginalLocalDomain s).algebra :=
  (a.originalRecognitionIndex s).originalDomain s Subset.rfl

@[simp]
theorem recognitionOriginalDomain_algebra (s : a.Index) :
    (a.recognitionOriginalDomain s).algebra = a.algebra s := rfl

/-- The literal original chart locus is an actual index after saturation
of the recognition atlas. -/
def recognitionOriginalSaturatedIndex (s : a.Index) : a.recognitionAtlas.saturatedAtlas.Index :=
  ⟨(a.recognitionOriginalLocalDomain s).locus, ⟨_, rfl⟩⟩

theorem recognitionOriginalSaturatedIndex_range (s : a.Index) :
    Set.range (a.recognitionAtlas.saturatedAtlas.chart
      (a.recognitionOriginalSaturatedIndex s)) = Set.range (a.chart s) :=
  (a.recognitionAtlas.range_saturatedChart _).trans (a.recognitionOriginalLocalDomain_locus s)

/-- The canonical equal-locus inclusion to the chosen saturated
representative retains its complete bounded restriction. -/
def recognitionOriginalToSaturated (s : a.Index) :
    a.recognitionOriginalLocalDomain s ⟶
      a.recognitionAtlas.saturatedRepresentative (a.recognitionOriginalSaturatedIndex s) :=
  (LocalDomain.isoOfLocusEq _ _
    (a.recognitionAtlas.saturatedRepresentative_locus
      (a.recognitionOriginalSaturatedIndex s)).symm).hom

/-- Compose actual full domains through the saturated presentation,
returning to the unchanged original chart algebra. -/
def recognitionOriginalSaturatedDomain (s : a.Index) :
    Domain K (a.recognitionAtlas.saturatedAtlas.algebra
      (a.recognitionOriginalSaturatedIndex s)) :=
  (a.recognitionOriginalToSaturated s).relativeDomain.extend (a.recognitionOriginalDomain s)

@[simp]
theorem recognitionOriginalSaturatedDomain_algebra (s : a.Index) :
    (a.recognitionOriginalSaturatedDomain s).algebra = a.algebra s := rfl

theorem recognitionOriginalSaturatedDomain_over_ambient (s : a.Index)
    (x : BanachSpectrum (a.algebra s)) :
    a.recognitionAtlas.saturatedAtlas.chart (a.recognitionOriginalSaturatedIndex s)
      ((a.recognitionOriginalSaturatedDomain s).spectrumMap x) = a.chart s x := by
  let q := a.recognitionOriginalToSaturated s
  let P := a.recognitionOriginalDomain s
  have hs : (q.relativeDomain.extend P).spectrumMap x =
      q.spectrumMap (P.spectrumMap x) := BanachSpectrum.ext fun _ => rfl
  exact (congrArg
    (a.recognitionAtlas.saturatedRepresentative (a.recognitionOriginalSaturatedIndex s)).ambientMap
    hs).trans ((q.ambientMap_naturality (P.spectrumMap x)).trans
      ((a.recognitionAtlas.originalLocalDomain_ambientMap
        (a.originalRecognitionIndex s) (P.spectrumMap x)).trans
          ((a.originalRecognitionIndex s).originalDomain_over_ambient s Subset.rfl x)))

/-- Original-chart restrictions commute with the actual local-domain
inclusions between their first recognized presentations, on all elements. -/
theorem recognitionOriginalDomain_restriction (s t : a.Index)
    (hst : Set.range (a.chart s) ⊆ Set.range (a.chart t))
    (f : a.recognitionOriginalLocalDomain s ⟶ a.recognitionOriginalLocalDomain t) :
    (a.recognitionOriginalDomain s).baseMap.comp f.restriction =
      (a.restriction s t hst).comp (a.recognitionOriginalDomain t).baseMap := by
  let U := a.originalRecognitionIndex s
  let V := a.originalRecognitionIndex t
  have hUV : Set.range (a.recognitionAtlas.chart U) ⊆
      Set.range (a.recognitionAtlas.chart V) :=
    U.range_chart.subset.trans (hst.trans V.range_chart.symm.subset)
  have hf : f.restriction = U.restriction V hst :=
    a.recognitionAtlas.originalLocalDomain_restriction U V hUV f
  have h₀ := U.originalRestriction_comp_restriction V hst s Subset.rfl
  have h₁ := V.originalRestriction_naturality t s Subset.rfl hst hst
  ext x
  exact (congrArg (fun q : BoundedAlgHom K V.algebra U.algebra =>
    (a.recognitionOriginalDomain s).baseMap (q x)) hf).trans
      ((congrArg (fun q : BoundedAlgHom K V.algebra (a.algebra s) => q x) h₀).trans
        (congrArg (fun q : BoundedAlgHom K V.algebra (a.algebra s) => q x) h₁).symm)

variable (W : a.recognitionAtlas.saturatedAtlas.RecognizedSubset)

/-- The original chosen saturated chart as a full domain in the actual
outer recognized algebra. -/
def recognitionChartOuterDomain (s : a.Index)
    (hs : Set.range (a.chart s) ⊆ W.locus) : Domain K W.algebra :=
  W.originalDomain (a.recognitionOriginalSaturatedIndex s)
    ((a.recognitionOriginalSaturatedIndex_range s).subset.trans hs)

/-- Every contained original chart has a canonical full domain over the
nested recognized algebra, with its original algebra unchanged. -/
def recognitionChartDomain (s : a.Index)
    (hs : Set.range (a.chart s) ⊆ W.locus) : Domain K W.algebra :=
  (a.recognitionChartOuterDomain W s hs).extend (a.recognitionOriginalSaturatedDomain s)

@[simp]
theorem recognitionChartDomain_algebra (s : a.Index)
    (hs : Set.range (a.chart s) ⊆ W.locus) :
    (a.recognitionChartDomain W s hs).algebra = a.algebra s := rfl

/-- All three structural restrictions are composed as entire bounded maps. -/
theorem recognitionChartDomain_baseMap (s : a.Index)
    (hs : Set.range (a.chart s) ⊆ W.locus) :
    (a.recognitionChartDomain W s hs).baseMap =
      ((a.recognitionOriginalDomain s).baseMap.comp
        (a.recognitionOriginalToSaturated s).restriction).comp
          (W.originalRestriction (a.recognitionOriginalSaturatedIndex s)
            ((a.recognitionOriginalSaturatedIndex_range s).subset.trans hs)) := rfl

theorem recognitionChartDomain_over_ambient (s : a.Index)
    (hs : Set.range (a.chart s) ⊆ W.locus) (x : BanachSpectrum (a.algebra s)) :
    W.chart ((a.recognitionChartDomain W s hs).spectrumMap x) = a.chart s x := by
  let C := a.recognitionChartOuterDomain W s hs
  let I := a.recognitionOriginalSaturatedDomain s
  have hc : (C.extend I).spectrumMap x = C.spectrumMap (I.spectrumMap x) :=
    BanachSpectrum.ext fun _ => rfl
  exact (congrArg W.chart hc).trans
    ((W.originalDomain_over_ambient (a.recognitionOriginalSaturatedIndex s) _
      (I.spectrumMap x)).trans (a.recognitionOriginalSaturatedDomain_over_ambient s x))

theorem recognitionChartDomain_locus (s : a.Index)
    (hs : Set.range (a.chart s) ⊆ W.locus) :
    (a.recognitionChartDomain W s hs).locus = W.chart ⁻¹' Set.range (a.chart s) := by
  let R := a.recognitionChartDomain W s hs
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := R.represents.2.1.symm ▸ hx
    exact ⟨y, (a.recognitionChartDomain_over_ambient W s hs y).symm.trans
      (congrArg W.chart hy)⟩
  · rintro ⟨y, hy⟩
    have h : R.spectrumMap y = x := W.isEmbedding_chart.injective
      ((a.recognitionChartDomain_over_ambient W s hs y).trans hy)
    exact h ▸ R.represents.hasImageIn y

/-- Full naturality of the canonical original-chart maps through both
atlas extensions; no algebra equality is inferred from spectrum values. -/
theorem recognitionChartDomain_naturality (s t : a.Index)
    (hs : Set.range (a.chart s) ⊆ W.locus)
    (ht : Set.range (a.chart t) ⊆ W.locus)
    (hst : Set.range (a.chart s) ⊆ Set.range (a.chart t)) :
    (a.restriction s t hst).comp (a.recognitionChartDomain W t ht).baseMap =
      (a.recognitionChartDomain W s hs).baseMap := by
  let S := a.recognitionOriginalSaturatedIndex s
  let T := a.recognitionOriginalSaturatedIndex t
  let L := a.recognitionOriginalLocalDomain s
  let M := a.recognitionOriginalLocalDomain t
  let q := a.recognitionOriginalToSaturated s
  let r := a.recognitionOriginalToSaturated t
  let f : L ⟶ M := LocalDomain.Inclusion.ofSubset _ _ (by
    rw [a.recognitionOriginalLocalDomain_locus, a.recognitionOriginalLocalDomain_locus]
    exact hst)
  have hST : Set.range (a.recognitionAtlas.saturatedAtlas.chart S) ⊆
      Set.range (a.recognitionAtlas.saturatedAtlas.chart T) :=
    (a.recognitionOriginalSaturatedIndex_range s).subset.trans
      (hst.trans (a.recognitionOriginalSaturatedIndex_range t).symm.subset)
  let g := a.recognitionAtlas.saturatedInclusion S T hST
  have hsq : f ≫ r = q ≫ g :=
    @Subsingleton.elim (LocalDomain.Inclusion L
      (a.recognitionAtlas.saturatedRepresentative T)) inferInstance _ _
  let ws := W.originalRestriction S ((a.recognitionOriginalSaturatedIndex_range s).subset.trans hs)
  let wt := W.originalRestriction T ((a.recognitionOriginalSaturatedIndex_range t).subset.trans ht)
  have hn : g.restriction.comp wt = ws :=
    W.originalRestriction_naturality T S _ _ hST
  ext x
  have hp := congrArg
    (fun h : BoundedAlgHom K M.algebra (a.algebra s) => h (r.restriction (wt x)))
    (a.recognitionOriginalDomain_restriction s t hst f)
  have hq := congrArg (fun h : L ⟶ a.recognitionAtlas.saturatedRepresentative T =>
    h.restriction (wt x)) hsq
  have hw := congrArg
    (fun h : BoundedAlgHom K W.algebra
      (a.recognitionAtlas.saturatedAtlas.algebra S) => h x) hn
  exact hp.symm.trans
    ((congrArg (a.recognitionOriginalDomain s).baseMap hq).trans
      (congrArg (fun y => (a.recognitionOriginalDomain s).baseMap (q.restriction y)) hw))

end Langlands.Analytic.IndexedAffinoidAtlas

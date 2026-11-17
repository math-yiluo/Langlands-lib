import Langlands.Geometry.Analytic.FullRecognitionPairSystems
import Langlands.Geometry.Analytic.FullRecognitionPairLocalCondition
import Langlands.Geometry.Analytic.CoherentQuasiIsoReverseSubatlas
import Langlands.Geometry.Analytic.CompatibleStrongSubatlasRefinement

/-! # Full recognition source charts admitting a recognized target -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

/-- Select exactly the recognized source charts whose full image lies in
some recognized target chart. -/
def recognitionSourceSelection (V : A.fullRecognitionPresentation.atlas.Index) : Prop :=
  ∃ W : B.fullRecognitionPresentation.atlas.Index,
    g.baseMap '' range (A.fullRecognitionPresentation.atlas.chart V) ⊆
      range (B.fullRecognitionPresentation.atlas.chart W)

/-- Every original local-domain chart, recognized by its singleton cover,
is selected. -/
theorem recognitionSourceSelection_original (i : A.atlas.saturatedAtlas.Index) :
    g.recognitionSourceSelection (A.atlas.saturatedAtlas.originalRecognitionIndex i) := by
  obtain ⟨j, hij⟩ := g.target_exists i
  refine ⟨B.atlas.saturatedAtlas.originalRecognitionIndex j, ?_⟩
  exact ((image_mono (A.atlas.saturatedAtlas.recognitionAtlas_original_range i).subset).trans
    hij).trans (B.atlas.saturatedAtlas.recognitionAtlas_original_range j).symm.subset

theorem recognitionSourceSelection_downward :
    A.fullRecognitionPresentation.atlas.IsDownwardClosedSelection
      g.recognitionSourceSelection := by
  intro V V' h
  rintro ⟨W, hW⟩
  exact ⟨W, (image_mono h).trans hW⟩

/-- The finite original-domain cover of each recognized source chart gives
relative local refinement by selected singleton-recognized charts. -/
theorem recognitionSourceSelection_locallyRefining :
    A.fullRecognitionPresentation.atlas.IsLocallyRefiningSelection
      g.recognitionSourceSelection := by
  rintro _ ⟨V, rfl⟩ x hx
  change A.atlas.saturatedAtlas.RecognizedSubset at V
  have hloc := (AtlasTopology.isQuasinet_restrictedFamily_iff
    (range (fun i => range (A.atlas.saturatedAtlas.chart i))) V.locus).mp
      V.val.isQuasinet_restrictedChartFamily
  obtain ⟨σ, hf, hs, hm, hn⟩ := hloc V.locus (mem_singleton _) x
    (V.range_chart.subset hx)
  refine ⟨σ, hf, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨i, hi⟩ := hs hU
    refine ⟨⟨A.atlas.saturatedAtlas.originalRecognitionIndex i,
      g.recognitionSourceSelection_original i⟩, ?_⟩
    exact (A.atlas.saturatedAtlas.recognitionAtlas_original_range i).trans hi
  · intro U hU
    exact ⟨(hm U hU).1.trans V.range_chart.symm.subset, (hm U hU).2⟩
  · exact (nhdsWithin_mono x V.range_chart.subset) hn

/-- The selected recognized source atlas keeps its literal space, original
recognized algebras, charts and all full restrictions. -/
def recognitionSource : AffinoidAtlasPresentation.{u, v, v} K :=
  A.fullRecognitionPresentation.subpresentation g.recognitionSourceSelection
    g.recognitionSourceSelection_locallyRefining

theorem recognitionSource_hasAllLocalDomains :
    g.recognitionSource.atlas.HasAllLocalDomains :=
  A.fullRecognitionPresentation.atlas.subatlas_hasAllLocalDomains
    A.fullRecognitionPresentation_hasAllLocalDomains g.recognitionSourceSelection
    g.recognitionSourceSelection_locallyRefining g.recognitionSourceSelection_downward

/-- Restrict the actual full-recognition pair system to the selected
source. Its selection property is precisely target existence. -/
def recognitionMap : StrongHom g.recognitionSource B.fullRecognitionPresentation where
  baseMap := g.baseMap
  target_exists V := V.property
  pullback V W h := g.fullRecognitionPairs.pullback V.val W h
  chart_comm V W h x := g.fullRecognitionPairs.chart_comm V.val W h x
  restriction_comm V V' W W' hVV' hWW' h h' :=
    g.fullRecognitionPairs.restriction_comm V.val V'.val W W' hVV' hWW' h h'

/-- The compatible map retains the complete all-pairs bounded system. -/
def compatibleRecognitionMap : CompatibleStrongHom g.recognitionSource
    B.fullRecognitionPresentation :=
  CompatibleStrongHom.ofSaturated g.recognitionMap g.recognitionSource_hasAllLocalDomains

/-- The forward comparison from local domains into selected recognition,
with every canonical original-chart restriction unchanged. -/
def recognitionSourceComparison : StrongHom A.saturatedPresentation g.recognitionSource where
  baseMap := ContinuousMap.id A.space
  target_exists i := by
    refine ⟨⟨A.atlas.saturatedAtlas.originalRecognitionIndex i,
      g.recognitionSourceSelection_original i⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (A.atlas.saturatedAtlas.recognitionAtlas_original_range i).symm.subset hx
  pullback i V h := A.localDomainToFullRecognition.pullback i V.val h
  chart_comm i V h x := A.localDomainToFullRecognition.chart_comm i V.val h x
  restriction_comm i i' V V' hii' hVV' h h' :=
    A.localDomainToFullRecognition.restriction_comm i i' V.val V'.val hii' hVV' h h'

theorem recognitionSourceComparison_isQuasiIso : g.recognitionSourceComparison.IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i V h
  exact A.localDomainToFullRecognition_isQuasiIso.2 i V.val h

/-- Retain the original source's intrinsic coefficient-test coherence. -/
def compatibleRecognitionSourceComparison : CompatibleStrongHom
    A.saturatedPresentation g.recognitionSource :=
  CompatibleStrongHom.ofSaturated g.recognitionSourceComparison
    A.atlas.saturatedAtlas_hasAllLocalDomains

@[simp]
theorem recognitionMap_baseMap : g.recognitionMap.baseMap = g.baseMap := rfl

@[simp]
theorem recognitionSourceComparison_baseMap :
    g.recognitionSourceComparison.baseMap = ContinuousMap.id A.space := rfl

/-- The forward comparison square commutes on complete strong maps. On
every old source chart, the full recognized pullback restricts to the old map. -/
theorem recognitionSourceComparison_comp :
    g.recognitionSourceComparison.saturatedComp g.recognitionMap
      A.atlas.saturatedAtlas_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains =
      g.toFullRecognitionTarget := by
  refine StrongHom.ext_of_saturated
    (f := g.recognitionSourceComparison.saturatedComp g.recognitionMap
      A.atlas.saturatedAtlas_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains)
    (g := g.toFullRecognitionTarget)
    A.atlas.saturatedAtlas_hasAllLocalDomains ?_ ?_
  · exact ContinuousMap.ext fun _ => rfl
  intro i
  obtain ⟨W, hiW⟩ := g.toFullRecognitionTarget.target_exists i
  let V : A.atlas.saturatedAtlas.RecognizedSubset :=
    A.atlas.saturatedAtlas.originalRecognitionIndex i
  have hiV : range (A.atlas.saturatedAtlas.chart i) ⊆ V.locus :=
    (A.atlas.saturatedAtlas.recognitionAtlas_original_range i).symm.subset.trans V.range_chart.subset
  have hVW : g.baseMap '' range V.chart ⊆ range W.chart :=
    (image_mono (A.atlas.saturatedAtlas.recognitionAtlas_original_range i).subset).trans hiW
  let I : g.recognitionSource.atlas.Index := ⟨V, W, hVW⟩
  have hiI : g.recognitionSourceComparison.baseMap '' range
      (A.saturatedPresentation.atlas.chart i) ⊆ range (g.recognitionSource.atlas.chart I) := by
    change _root_.id '' range (A.atlas.saturatedAtlas.chart i) ⊆ range V.chart
    rw [image_id]
    exact (A.atlas.saturatedAtlas.recognitionAtlas_original_range i).symm.subset
  refine ⟨W, hiW, ?_⟩
  rw [StrongHom.saturatedComp_pullback g.recognitionSourceComparison g.recognitionMap
    A.atlas.saturatedAtlas_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    i I W hiI hVW hiW]
  exact g.toFullRecognitionTarget.originalRestriction_comp_recognizedSourceExtension V W hVW i hiV

/-- Every supplied admissible recognized pair is a literal pair of
original indices for the constructed selected map, with unchanged algebra map. -/
def recognitionSourceIndex (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' range V.chart ⊆ range W.chart) : g.recognitionSource.atlas.Index :=
  ⟨V, W, h⟩

@[simp]
theorem recognitionMap_pullback
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' range V.chart ⊆ range W.chart) :
    g.recognitionMap.pullback (g.recognitionSourceIndex V W h) W h =
      g.fullRecognitionPairs.pullback V W h := rfl

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic

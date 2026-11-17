import Langlands.Geometry.Analytic.RecognizedContainedMap
import Langlands.Geometry.Analytic.FiniteMorphismSmallNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Statement
import Langlands.Geometry.Analytic.QuasiIsoSourceEtale

/-! # Recognition and finiteness of actual affinoid inverse images -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (hW : W.locus ⊆ range (B.atlas.saturatedAtlas.chart j))
    (hij : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))

/-- An existing saturated chart for the actual full-domain inverse image. -/
def recognizedPullbackChart : A.atlas.saturatedAtlas.Index :=
  Classical.choose (A.atlas.saturatedAtlas_hasAllLocalDomains.exists_chart
    (⟨i, Domain.pullback (g.pullback i j hij) (W.containedDomain j hW)⟩ :
      LocalDomain A.atlas.saturatedAtlas))

/-- Recognize the actual inverse image inside the chosen original source chart. -/
def recognizedPullback : A.atlas.saturatedAtlas.RecognizedSubset :=
  A.atlas.saturatedAtlas.originalRecognitionIndex
    (g.recognizedPullbackChart W i j hW hij)

theorem recognizedPullback_locus :
    (g.recognizedPullback W i j hW hij).locus =
      range (A.atlas.saturatedAtlas.chart i) ∩ g.baseMap ⁻¹' W.locus := by
  have hr := Classical.choose_spec
    (A.atlas.saturatedAtlas_hasAllLocalDomains.exists_chart
      (⟨i, Domain.pullback (g.pullback i j hij) (W.containedDomain j hW)⟩ :
        LocalDomain A.atlas.saturatedAtlas))
  change range (A.atlas.saturatedAtlas.chart
    (g.recognizedPullbackChart W i j hW hij)) = _
  rw [show range (A.atlas.saturatedAtlas.chart
      (g.recognizedPullbackChart W i j hW hij)) =
      (⟨i, Domain.pullback (g.pullback i j hij) (W.containedDomain j hW)⟩ :
        LocalDomain A.atlas.saturatedAtlas).locus from hr]
  change A.atlas.saturatedAtlas.chart i ''
    (Domain.pullback (g.pullback i j hij) (W.containedDomain j hW)).locus = _
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨mem_range_self x, ?_⟩
    change B.atlas.saturatedAtlas.chart j
      (BanachSpectrum.comap (g.pullback i j hij).toBoundedRingHom x) ∈ W.locus at hx
    erw [g.chart_comm i j hij x] at hx
    exact hx
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    change B.atlas.saturatedAtlas.chart j
      (BanachSpectrum.comap (g.pullback i j hij).toBoundedRingHom x) ∈ W.locus
    erw [g.chart_comm i j hij x]
    exact hx

theorem recognizedPullback_admissible :
    g.baseMap '' range (g.recognizedPullback W i j hW hij).chart ⊆ range W.chart := by
  rintro _ ⟨x, hx, rfl⟩
  have hxV := (g.recognizedPullback W i j hW hij).range_chart.subset hx
  have hxpre := (g.recognizedPullback_locus W i j hW hij).subset hxV
  exact W.range_chart.symm.subset hxpre.2

include hW hij in
/-- A finite original bounded map makes every recognized inverse-image map finite. -/
theorem fullRecognitionPairs_isFiniteBanach_of_pushout
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (hfin : (g.pullback i j hij).IsFiniteBanach)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (hV : V.locus ⊆ range (A.atlas.saturatedAtlas.chart i))
    (hVW : g.baseMap '' range V.chart ⊆ range W.chart)
    (hpre : V.locus = range (A.atlas.saturatedAtlas.chart i) ∩ g.baseMap ⁻¹' W.locus) :
    (g.fullRecognitionPairs.pullback V W hVW).IsFiniteBanach := by
  rw [g.fullRecognitionPairs_pullback_eq_pushout V W i j hV hW hij hVW hpre]
  exact (g.fullRecognitionPullbackEquiv V W i j hV hW hij hpre).isFiniteBanach.comp
    (hpush _ _ _ (g.pullback i j hij) (W.containedRestriction j hW) hfin)

/-- A finite bounded map in global source and target charts is a finite
morphism in the full-recognition sense, conditional on finite Banach base change. -/
theorem isFinite_of_globalCharts
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (hi : range (A.atlas.saturatedAtlas.chart i) = univ)
    (hj : range (B.atlas.saturatedAtlas.chart j) = univ)
    (hfin : (g.pullback i j hij).IsFiniteBanach) : g.IsFinite := by
  refine ⟨subset_univ _, fun W' _ => ?_⟩
  have hW' : W'.locus ⊆ range (B.atlas.saturatedAtlas.chart j) := by
    rw [hj]
    exact subset_univ _
  let V := g.recognizedPullback W' i j hW' hij
  have hV := g.recognizedPullback_locus W' i j hW' hij
  have hadm := g.recognizedPullback_admissible W' i j hW' hij
  refine ⟨V, hadm, ?_, g.fullRecognitionPairs_isFiniteBanach_of_pushout
    W' i j hW' hij hpush hfin V (hV.subset.trans inter_subset_left) hadm hV⟩
  rw [hV, hi]

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic

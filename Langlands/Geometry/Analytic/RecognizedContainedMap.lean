import Langlands.Geometry.Analytic.RecognizedContainedDomain
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation

/-! # Full bounded squares for recognized subsets inside original charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas.RecognizedSubset

variable {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- Contained restrictions commute with the complete recognized restriction. -/
theorem restriction_comp_containedRestriction (V W : a.RecognizedSubset)
    (hVW : V.locus ⊆ W.locus) (j : a.Index) (hW : W.locus ⊆ range (a.chart j)) :
    (V.restriction W hVW).comp (W.containedRestriction j hW) =
      V.containedRestriction j (hVW.trans hW) := by
  apply V.hom_ext
  intro k hk
  calc
    (V.originalRestriction k hk).comp
        ((V.restriction W hVW).comp (W.containedRestriction j hW)) =
      (W.originalRestriction k (hk.trans hVW)).comp (W.containedRestriction j hW) :=
        congrArg (fun q => q.comp (W.containedRestriction j hW))
          (V.originalRestriction_comp_restriction W hVW k hk)
    _ = a.restriction k j ((hk.trans hVW).trans hW) :=
      W.originalRestriction_comp_containedRestriction j hW k (hk.trans hVW)
    _ = (V.originalRestriction k hk).comp
        (V.containedRestriction j (hVW.trans hW)) :=
      (V.originalRestriction_comp_containedRestriction j (hVW.trans hW) k hk).symm

end IndexedAffinoidAtlas.RecognizedSubset

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

/-- The full-recognition bounded map commutes with the structural maps of
recognized subsets contained in admissible original source and target charts. -/
theorem fullRecognitionPairs_comp_containedRestriction
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (hV : V.locus ⊆ range (A.atlas.saturatedAtlas.chart i))
    (hW : W.locus ⊆ range (B.atlas.saturatedAtlas.chart j))
    (hij : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (hVW : g.baseMap '' range V.chart ⊆ range W.chart) :
    (g.fullRecognitionPairs.pullback V W hVW).comp (W.containedRestriction j hW) =
      (V.containedRestriction i hV).comp (g.pullback i j hij) := by
  let J : B.atlas.saturatedAtlas.RecognizedSubset :=
    B.atlas.saturatedAtlas.originalRecognitionIndex j
  have hJ : J.locus = range (B.atlas.saturatedAtlas.chart j) := rfl
  have hWJ : W.locus ⊆ J.locus := hW.trans hJ.symm.subset
  have hVJ : g.baseMap '' range V.chart ⊆ range J.chart :=
    hVW.trans (W.range_chart.subset.trans (hWJ.trans J.range_chart.symm.subset))
  have hVV : range V.chart ⊆ range V.chart := Subset.rfl
  have hWJr : range W.chart ⊆ range J.chart :=
    W.range_chart.subset.trans (hWJ.trans J.range_chart.symm.subset)
  have hp := g.fullRecognitionPairs.restriction_comm V V W J hVV hWJr hVW hVJ
  change (V.restriction V Subset.rfl).comp (g.fullRecognitionPairs.pullback V J hVJ) =
    (g.fullRecognitionPairs.pullback V W hVW).comp (W.restriction J hWJ) at hp
  rw [V.restriction_self] at hp
  change (g.fullRecognitionPairs.pullback V J hVJ) =
    (g.fullRecognitionPairs.pullback V W hVW).comp (W.restriction J hWJ) at hp
  have hc := W.restriction_comp_containedRestriction J hWJ j hJ.subset
  have hfactor :
      (g.fullRecognitionPairs.pullback V W hVW).comp (W.containedRestriction j hW) =
        (g.fullRecognitionPairs.pullback V J hVJ).comp (J.containedRestriction j hJ.subset) := by
    calc
      _ = (g.fullRecognitionPairs.pullback V W hVW).comp
          ((W.restriction J hWJ).comp (J.containedRestriction j hJ.subset)) :=
        congrArg (fun q => (g.fullRecognitionPairs.pullback V W hVW).comp q) hc.symm
      _ = _ := congrArg (fun q => q.comp (J.containedRestriction j hJ.subset)) hp.symm
  rw [hfactor]
  apply V.hom_ext
  intro k hk
  have hkV : range (A.atlas.saturatedAtlas.chart k) ⊆ range V.chart :=
    hk.trans V.range_chart.symm.subset
  have hkj : g.baseMap '' range (A.atlas.saturatedAtlas.chart k) ⊆
      range (B.atlas.saturatedAtlas.chart j) := (image_mono (hk.trans hV)).trans hij
  have hji : range (B.atlas.saturatedAtlas.chart j) ⊆ J.locus := hJ.symm.subset
  have hrec := g.originalRestriction_comp_fullRecognitionPairs V J hVJ k hk j hji hkj
  have hid := J.originalRestriction_comp_containedRestriction j hJ.subset j hji
  rw [B.atlas.saturatedAtlas.restriction_id] at hid
  have hcomm := g.restriction_comm k i j j (hk.trans hV) Subset.rfl hkj hij
  erw [B.saturatedPresentation.atlas.restriction_id, BoundedAlgHom.comp_id] at hcomm
  apply BoundedAlgHom.ext
  intro x
  have hxrec := congrArg (fun q => q (J.containedRestriction j hJ.subset x)) hrec
  have hxid := congrArg (fun q => q x) hid
  have hxcomm := congrArg (fun q => q x) hcomm.symm
  have hxcont := congrArg (fun q => q (g.pullback i j hij x))
    (V.originalRestriction_comp_containedRestriction i hV k hk).symm
  exact hxrec.trans ((congrArg (g.pullback k j hkj) hxid).trans (hxcomm.trans hxcont))

/-- The original affinoid pushout and the recognized inverse image have the
same full-domain locus in the chosen source chart. -/
theorem pullback_containedDomain_locus
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (hV : V.locus ⊆ range (A.atlas.saturatedAtlas.chart i))
    (hW : W.locus ⊆ range (B.atlas.saturatedAtlas.chart j))
    (hij : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (hpre : V.locus = range (A.atlas.saturatedAtlas.chart i) ∩
      g.baseMap ⁻¹' W.locus) :
    (Domain.pullback (g.pullback i j hij) (W.containedDomain j hW)).locus =
      (V.containedDomain i hV).locus := by
  ext x
  change (B.atlas.saturatedAtlas.chart j
    (BanachSpectrum.comap (g.pullback i j hij).toBoundedRingHom x) ∈ W.locus) ↔
    A.atlas.saturatedAtlas.chart i x ∈ V.locus
  erw [g.chart_comm i j hij x, hpre]
  exact ⟨fun h => ⟨mem_range_self x, h⟩, fun h => h.2⟩

/-- A full bounded comparison between the actual affinoid pushout algebra and
the unchanged algebra of the recognized inverse image. -/
def fullRecognitionPullbackEquiv
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (hV : V.locus ⊆ range (A.atlas.saturatedAtlas.chart i))
    (hW : W.locus ⊆ range (B.atlas.saturatedAtlas.chart j))
    (hij : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (hpre : V.locus = range (A.atlas.saturatedAtlas.chart i) ∩
      g.baseMap ⁻¹' W.locus) :
    BoundedAlgEquiv K
      (Domain.pullback (g.pullback i j hij) (W.containedDomain j hW)).algebra V.algebra :=
  Domain.boundedEquivOfLocusEq _ _
    (g.pullback_containedDomain_locus V W i j hV hW hij hpre)

/-- The comparison identifies the complete recognized pullback with the original
second pushout leg, rather than only comparing their point functions. -/
theorem fullRecognitionPairs_pullback_eq_pushout
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (hV : V.locus ⊆ range (A.atlas.saturatedAtlas.chart i))
    (hW : W.locus ⊆ range (B.atlas.saturatedAtlas.chart j))
    (hij : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (hVW : g.baseMap '' range V.chart ⊆ range W.chart)
    (hpre : V.locus = range (A.atlas.saturatedAtlas.chart i) ∩
      g.baseMap ⁻¹' W.locus) :
    g.fullRecognitionPairs.pullback V W hVW =
      (g.fullRecognitionPullbackEquiv V W i j hV hW hij hpre).toBoundedAlgHom.comp
        (Domain.pullbackMap (g.pullback i j hij) (W.containedDomain j hW)) := by
  apply (W.containedDomain j hW).represents.hom_ext V.algebra
  have hs := g.fullRecognitionPairs_comp_containedRestriction V W i j hV hW hij hVW
  have hE := Domain.boundedEquivOfLocusEq_comp_baseMap
    (Domain.pullback (g.pullback i j hij) (W.containedDomain j hW))
    (V.containedDomain i hV)
    (g.pullback_containedDomain_locus V W i j hV hW hij hpre)
  have hpb := Domain.pullbackMap_comp_baseMap (g.pullback i j hij)
    (W.containedDomain j hW)
  apply BoundedAlgHom.ext
  intro x
  exact (congrArg (fun q => q x) hs).trans
    ((congrArg (fun q => q (g.pullback i j hij x)) hE.symm).trans
      (congrArg (g.fullRecognitionPullbackEquiv V W i j hV hW hij hpre)
        (congrArg (fun q => q x) hpb.symm)))

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic

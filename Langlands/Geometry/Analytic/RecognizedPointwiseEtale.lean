import Langlands.Geometry.Analytic.RecognizedFinitePullback
import Langlands.Geometry.Analytic.AffinoidPointwiseBaseChange
import Langlands.Geometry.Analytic.FullRecognitionEtaleComposition

/-! # Pointwise étaleness of recognized inverse images -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (i : A.atlas.saturatedAtlas.Index) (j : B.atlas.saturatedAtlas.Index)
    (hV : V.locus ⊆ range (A.atlas.saturatedAtlas.chart i))
    (hW : W.locus ⊆ range (B.atlas.saturatedAtlas.chart j))
    (hij : g.baseMap '' range (A.atlas.saturatedAtlas.chart i) ⊆
      range (B.atlas.saturatedAtlas.chart j))
    (hpre : V.locus = range (A.atlas.saturatedAtlas.chart i) ∩ g.baseMap ⁻¹' W.locus)

/-- The point of the actual pushout corresponding to a recognized source point. -/
def recognizedPullbackPoint (s : BanachSpectrum V.algebra) :
    BanachSpectrum (Domain.pullback (g.pullback i j hij) (W.containedDomain j hW)).algebra :=
  BanachSpectrum.comap
    (g.fullRecognitionPullbackEquiv V W i j hV hW hij hpre).toBoundedAlgHom.toBoundedRingHom s

/-- The first pushout projection recovers the same ambient source point. -/
theorem chart_recognizedPullbackPoint (s : BanachSpectrum V.algebra) :
    A.atlas.saturatedAtlas.chart i
      (BanachSpectrum.comap
        (AffinoidPushout.leftMap (g.pullback i j hij)
          (W.containedRestriction j hW)).toBoundedRingHom
        (g.recognizedPullbackPoint V W i j hV hW hij hpre s)) = V.chart s := by
  have hE := Domain.boundedEquivOfLocusEq_comp_baseMap
    (Domain.pullback (g.pullback i j hij) (W.containedDomain j hW))
    (V.containedDomain i hV)
    (g.pullback_containedDomain_locus V W i j hV hW hij hpre)
  have hp :
      BanachSpectrum.comap
        (AffinoidPushout.leftMap (g.pullback i j hij)
          (W.containedRestriction j hW)).toBoundedRingHom
        (g.recognizedPullbackPoint V W i j hV hW hij hpre s) =
      BanachSpectrum.comap (V.containedRestriction i hV).toBoundedRingHom s := by
    apply BanachSpectrum.ext
    intro a
    exact congrArg (fun q : BoundedAlgHom K (A.atlas.saturatedAtlas.algebra i)
      V.algebra => s (q a)) hE
  exact (congrArg (A.atlas.saturatedAtlas.chart i) hp).trans
    (V.chart_containedRestriction i hV s)

/-- Transfer étaleness at a source point through the actual tensor comparison
and the bounded equivalence of the two inverse-image algebras. -/
theorem fullRecognitionPairs_isEtaleAtPoint_of_pushout
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hfin : (g.pullback i j hij).IsFiniteBanach)
    (hVW : g.baseMap '' range V.chart ⊆ range W.chart)
    (s : BanachSpectrum V.algebra)
    (hs : (g.pullback i j hij).IsEtaleAtPoint
      (BanachSpectrum.comap
        (AffinoidPushout.leftMap (g.pullback i j hij)
          (W.containedRestriction j hW)).toBoundedRingHom
        (g.recognizedPullbackPoint V W i j hV hW hij hpre s))) :
    (g.fullRecognitionPairs.pullback V W hVW).IsEtaleAtPoint s := by
  let E := g.fullRecognitionPullbackEquiv V W i j hV hW hij hpre
  have hE := BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
    E.toBoundedAlgHom E.toAlgEquiv.bijective
  have hr := AffinoidPushout.rightMap_isEtaleAtPoint_of_tensorComparison
    (g.pullback i j hij) (W.containedRestriction j hW)
    (htensor _ _ _ (g.pullback i j hij) (W.containedRestriction j hW) hfin)
    hfin.finite.finiteType (g.recognizedPullbackPoint V W i j hV hW hij hpre s) hs
  rw [g.fullRecognitionPairs_pullback_eq_pushout V W i j hV hW hij hVW hpre]
  exact (hE.isEtaleAtPoint s).comp hE.1.finiteType
    (hpush _ _ _ (g.pullback i j hij) (W.containedRestriction j hW) hfin).finite.finiteType hr

/-- An open locus of pointwise étaleness in a finite global chart pair is an
open locus of étaleness over every recognized affinoid piece. -/
theorem isEtaleAtAllPieces_of_globalCharts
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hi : range (A.atlas.saturatedAtlas.chart i) = univ)
    (hj : range (B.atlas.saturatedAtlas.chart j) = univ)
    (hfin : (g.pullback i j hij).IsFiniteBanach)
    (O : Set A.space) (hO : IsOpen O)
    (het : ∀ t : BanachSpectrum (A.atlas.saturatedAtlas.algebra i),
      A.atlas.saturatedAtlas.chart i t ∈ O → (g.pullback i j hij).IsEtaleAtPoint t)
    {y : A.space} (hy : y ∈ O) : g.IsEtaleAtAllPieces y := by
  have hgf := g.isFinite_of_globalCharts i j hij hpush hi hj hfin
  have hpieces : ∀ (W' : B.atlas.saturatedAtlas.RecognizedSubset)
      (V' : A.atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' range V'.chart ⊆ range W'.chart),
      V'.locus = univ ∩ g.baseMap ⁻¹' W'.locus →
      ∀ s : BanachSpectrum V'.algebra, V'.chart s ∈ O →
        (g.fullRecognitionPairs.pullback V' W' h).IsEtaleAtPoint s := by
    intro W' V' h hpre' s hs
    have hV' : V'.locus ⊆ range (A.atlas.saturatedAtlas.chart i) := by
      rw [hi]
      exact subset_univ _
    have hW' : W'.locus ⊆ range (B.atlas.saturatedAtlas.chart j) := by
      rw [hj]
      exact subset_univ _
    have hpre'' : V'.locus =
        range (A.atlas.saturatedAtlas.chart i) ∩ g.baseMap ⁻¹' W'.locus := by
      rw [hi]
      exact hpre'
    apply g.fullRecognitionPairs_isEtaleAtPoint_of_pushout V' W' i j hV' hW' hij
      hpre'' hpush htensor hfin h s
    apply het
    exact (g.chart_recognizedPullbackPoint V' W' i j hV' hW' hij hpre'' s).symm ▸ hs
  refine ⟨O, hO, hy, fun y' hy' => ⟨?_, ?_⟩⟩
  · refine ⟨univ, univ, isOpen_univ, isOpen_univ, mem_univ _, hgf, ?_⟩
    intro W' _ _ V' h hpre' s hs
    exact (hpieces W' V' h hpre' s (hs.symm ▸ hy')).2
  · refine ⟨univ, univ, isOpen_univ, isOpen_univ, mem_univ _, hgf, ?_⟩
    intro W' _ _ V' h hpre' s hs
    exact (hpieces W' V' h hpre' s (hs.symm ▸ hy')).1

/-- Pointwise étaleness everywhere in a finite global chart pair realizes an
étale strong map for the all-pieces definition used by the actual site. -/
theorem isEtaleAllPieces_of_globalCharts
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    (hi : range (A.atlas.saturatedAtlas.chart i) = univ)
    (hj : range (B.atlas.saturatedAtlas.chart j) = univ)
    (hfin : (g.pullback i j hij).IsFiniteBanach)
    (het : ∀ t, (g.pullback i j hij).IsEtaleAtPoint t) : g.IsEtaleAllPieces :=
  fun _ => g.isEtaleAtAllPieces_of_globalCharts i j hij hpush htensor hi hj hfin
    univ isOpen_univ (fun t _ => het t) (mem_univ _)

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic

import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCancellation

/-! # Actual pullback squares between nested recognized affinoid pieces -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
  (P₀ P : A.atlas.saturatedAtlas.RecognizedSubset)
  (W₀ W : B.atlas.saturatedAtlas.RecognizedSubset)
  (h₀ : g.baseMap '' range P₀.chart ⊆ range W₀.chart)
  (hW : W.locus ⊆ W₀.locus)
  (hP : P.locus ⊆ P₀.locus)
  (hpre : P.locus = P₀.locus ∩ g.baseMap ⁻¹' W.locus)

include hpre

/-- The actual domain pullback has exactly the relative locus of the supplied
recognized inverse image. -/
theorem recognizedNestedPullback_locus :
    (Domain.pullback (g.fullRecognitionPairs.pullback P₀ W₀ h₀)
      (W.inclusionDomain W₀ hW)).locus =
      (P.inclusionDomain P₀ hP).locus := by
  ext x
  change W₀.chart
      (BanachSpectrum.comap
        (g.fullRecognitionPairs.pullback P₀ W₀ h₀).toBoundedRingHom x) ∈ W.locus ↔
    P₀.chart x ∈ P.locus
  have hc : W₀.chart
      (BanachSpectrum.comap
        (g.fullRecognitionPairs.pullback P₀ W₀ h₀).toBoundedRingHom x) =
      g.baseMap (P₀.chart x) :=
    g.fullRecognitionPairs.chart_comm P₀ W₀ h₀ x
  constructor
  · intro hx
    have hx' : g.baseMap (P₀.chart x) ∈ W.locus := hc ▸ hx
    exact hpre.symm ▸ ⟨P₀.range_chart ▸ mem_range_self x, hx'⟩
  · intro hx
    exact hc.symm ▸ (hpre ▸ hx).2

/-- The original affinoid pushout algebra is boundedly equivalent to the
unchanged algebra of the recognized inverse image, for arbitrary nested
recognized pieces. -/
def recognizedNestedPullbackEquiv :
    BoundedAlgEquiv K
      (AffinoidPushout.algebra (g.fullRecognitionPairs.pullback P₀ W₀ h₀)
        (W.restriction W₀ hW)) P.algebra :=
  Domain.boundedEquivOfLocusEq _ _
    (g.recognizedNestedPullback_locus P₀ P W₀ W h₀ hW hP hpre)

/-- The algebra comparison retains the full original source restriction. -/
theorem recognizedNestedPullbackEquiv_comp_leftMap :
    (g.recognizedNestedPullbackEquiv P₀ P W₀ W h₀ hW hP hpre).toBoundedAlgHom.comp
      (AffinoidPushout.leftMap (g.fullRecognitionPairs.pullback P₀ W₀ h₀)
        (W.restriction W₀ hW)) = P.restriction P₀ hP :=
  Domain.boundedEquivOfLocusEq_comp_baseMap _ _
    (g.recognizedNestedPullback_locus P₀ P W₀ W h₀ hW hP hpre)

/-- The comparison identifies the whole recognized pullback map with the
second leg of the actual affinoid pushout. -/
theorem fullRecognitionPairs_nestedPullback_eq_pushout
    (h : g.baseMap '' range P.chart ⊆ range W.chart) :
    g.fullRecognitionPairs.pullback P W h =
      (g.recognizedNestedPullbackEquiv P₀ P W₀ W h₀ hW hP hpre).toBoundedAlgHom.comp
        (AffinoidPushout.rightMap (g.fullRecognitionPairs.pullback P₀ W₀ h₀)
          (W.restriction W₀ hW)) := by
  apply (W.inclusionDomain W₀ hW).represents.hom_ext P.algebra
  have hPr : range P.chart ⊆ range P₀.chart := by
    rw [P.range_chart, P₀.range_chart]
    exact hP
  have hWr : range W.chart ⊆ range W₀.chart := by
    rw [W.range_chart, W₀.range_chart]
    exact hW
  have hc := g.fullRecognitionPairs.restriction_comm P P₀ W W₀ hPr hWr h h₀
  change (P.restriction P₀ hP).comp (g.fullRecognitionPairs.pullback P₀ W₀ h₀) =
    (g.fullRecognitionPairs.pullback P W h).comp (W.restriction W₀ hW) at hc
  have he := g.recognizedNestedPullbackEquiv_comp_leftMap P₀ P W₀ W h₀ hW hP hpre
  have hb := Domain.pullbackMap_comp_baseMap
    (g.fullRecognitionPairs.pullback P₀ W₀ h₀) (W.inclusionDomain W₀ hW)
  change (AffinoidPushout.rightMap _ _).comp (W.restriction W₀ hW) =
    (AffinoidPushout.leftMap _ _).comp (g.fullRecognitionPairs.pullback P₀ W₀ h₀) at hb
  apply BoundedAlgHom.ext
  intro a
  exact (congrArg (fun q => q a) hc.symm).trans
    ((congrArg (fun q => q (g.fullRecognitionPairs.pullback P₀ W₀ h₀ a)) he.symm).trans
      (congrArg (g.recognizedNestedPullbackEquiv P₀ P W₀ W h₀ hW hP hpre)
        (congrArg (fun q => q a) hb.symm)))

/-- The comparison carries each source point to a pushout point above its
original point in the containing source chart. -/
theorem recognizedNestedPullbackEquiv_chart
    (s : BanachSpectrum P.algebra) :
    P₀.chart (BanachSpectrum.comap
      (AffinoidPushout.leftMap (g.fullRecognitionPairs.pullback P₀ W₀ h₀)
        (W.restriction W₀ hW)).toBoundedRingHom
      ((g.recognizedNestedPullbackEquiv P₀ P W₀ W h₀ hW hP hpre).spectrumHomeomorph s)) =
      P.chart s := by
  change P₀.chart (BanachSpectrum.comap
    ((g.recognizedNestedPullbackEquiv P₀ P W₀ W h₀ hW hP hpre).toBoundedAlgHom.comp
      (AffinoidPushout.leftMap (g.fullRecognitionPairs.pullback P₀ W₀ h₀)
        (W.restriction W₀ hW))).toBoundedRingHom s) = _
  rw [g.recognizedNestedPullbackEquiv_comp_leftMap P₀ P W₀ W h₀ hW hP hpre]
  exact P.chart_restriction P₀ hP s

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

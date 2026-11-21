import Langlands.Geometry.Analytic.FullRecognitionChartMorphisms
import Langlands.Geometry.Analytic.FiniteEtaleOverRecognition
import Langlands.Geometry.Analytic.AffineAnalytificationFiniteCharts

/-! # Affinoid charts cut out of finite étale open neighborhoods -/

noncomputable section

universe u

namespace Langlands.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open SaturatedAtlasPresentation IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type u} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, u, u} K X)

private theorem isClopen_chart_preimage_of_isCompact_inter
    (L : a.saturatedAtlas.RecognizedSubset) {E : Set X}
    (hE : IsOpen E) (hc : IsCompact (L.locus ∩ E)) : IsClopen (L.chart ⁻¹' E) := by
  have hCompact : IsCompact (L.chart ⁻¹' E) := by
    rw [L.isEmbedding_chart.isCompact_iff, image_preimage_eq_inter_range, L.range_chart, inter_comm]
    exact hc
  exact ⟨hCompact.isClosed, hE.preimage L.chart.continuous⟩

/-- A compact open cut in a recognized chart, as a recognized chart in the full atlas. -/
def compactOpenChartPiece (L : a.saturatedAtlas.RecognizedSubset) {E : Set X}
    (hE : IsOpen E) (hc : IsCompact (L.locus ∩ E)) : a.saturatedAtlas.RecognizedSubset :=
  a.fullRecognitionDomainRecognizedSubset L
    (clopenRationalChart (L.chart ⁻¹' E) (a.isClopen_chart_preimage_of_isCompact_inter L hE hc)).toDomain

theorem compactOpenChartPiece_locus (L : a.saturatedAtlas.RecognizedSubset) {E : Set X}
    (hE : IsOpen E) (hc : IsCompact (L.locus ∩ E)) :
    (a.compactOpenChartPiece L hE hc).locus = L.locus ∩ E := by
  rw [compactOpenChartPiece, fullRecognitionDomainRecognizedSubset_locus]
  change L.chart '' (clopenRationalChart (L.chart ⁻¹' E) _).locus = _
  rw [locus_clopenRationalChart, image_preimage_eq_inter_range, L.range_chart, inter_comm]

set_option backward.isDefEq.respectTransparency false in
theorem compactOpenChartPiece_restriction (L : a.saturatedAtlas.RecognizedSubset) {E : Set X}
    (hE : IsOpen E) (hc : IsCompact (L.locus ∩ E))
    (h : (a.compactOpenChartPiece L hE hc).locus ⊆ L.locus) :
    ((a.compactOpenChartPiece L hE hc).restriction L h).IsFiniteBanach ∧
      ((a.compactOpenChartPiece L hE hc).restriction L h).AlgebraicallyFiniteEtale := by
  let R := a.compactOpenChartPiece L hE hc
  have hcl : IsClopen (L.chart ⁻¹' R.locus) := by
    change IsClopen (L.chart ⁻¹' (a.compactOpenChartPiece L hE hc).locus)
    rw [a.compactOpenChartPiece_locus L hE hc, preimage_inter, ← L.range_chart,
      preimage_range, univ_inter]
    exact a.isClopen_chart_preimage_of_isCompact_inter L hE hc
  have hfin := R.restriction_finite L h hcl
  exact ⟨AffineAnalytification.FiniteCharts.isFiniteBanach_of_finite _ hfin,
    (R.restriction L h).algebraicallyFiniteEtale_of_isEtaleAtPoint hfin
      (R.restriction_isEtaleAtPoint L h hcl)⟩

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, u, u} K}
  {q : StrongHom A.saturatedPresentation B.saturatedPresentation}

set_option backward.isDefEq.respectTransparency false in
/-- The cut of the cover over a chart of its open image is a finite étale
surjective affinoid cover if the cut is compact inside a larger recognized piece. -/
theorem IsFiniteEtaleOver.exists_chartCover_of_openCut [T2Space B.space]
    {D E : Set A.space} {U : Set B.space} (hq : q.IsFiniteEtaleOver D U)
    (hE : IsOpen E) (hED : E ⊆ D)
    (P : A.atlas.saturatedAtlas.RecognizedSubset) (J : B.atlas.saturatedAtlas.RecognizedSubset)
    (hJU : J.locus ⊆ U) (hJE : J.locus ⊆ q.baseMap '' E)
    (hcut : E ∩ q.baseMap ⁻¹' J.locus = P.locus ∩ q.baseMap ⁻¹' J.locus) :
    ∃ (R : A.atlas.saturatedAtlas.RecognizedSubset) (_ : R.locus ⊆ P.locus)
      (hRJ : q.baseMap '' range R.chart ⊆ range J.chart),
      (q.fullRecognitionPairs.pullback R J hRJ).IsFiniteBanach ∧
        (q.fullRecognitionPairs.pullback R J hRJ).AlgebraicallyFiniteEtale ∧
        Function.Surjective (BanachSpectrum.comap
          (q.fullRecognitionPairs.pullback R J hRJ).toBoundedRingHom) := by
  obtain ⟨L, hLJ, hL, hqL⟩ := hq.2 J hJU
  have hLE : L.locus ∩ E = E ∩ q.baseMap ⁻¹' J.locus := by
    rw [hL]
    exact Set.ext fun _ => ⟨fun ⟨⟨_, hJ⟩, hE⟩ => ⟨hE, hJ⟩,
      fun ⟨hE, hJ⟩ => ⟨⟨hED hE, hJ⟩, hE⟩⟩
  have hc : IsCompact (L.locus ∩ E) := by
    rw [hLE, hcut]
    have hcP : IsCompact P.locus := isCompact_iff_compactSpace.2 inferInstance
    have hcJ : IsCompact J.locus := isCompact_iff_compactSpace.2 inferInstance
    exact hcP.inter_right (hcJ.isClosed.preimage q.baseMap.continuous)
  let R := A.atlas.compactOpenChartPiece L hE hc
  have hR : R.locus = E ∩ q.baseMap ⁻¹' J.locus :=
    (A.atlas.compactOpenChartPiece_locus L hE hc).trans hLE
  have hRP : R.locus ⊆ P.locus := (hR.trans hcut).trans_subset inter_subset_left
  have hRL : R.locus ⊆ L.locus :=
    (A.atlas.compactOpenChartPiece_locus L hE hc).trans_subset inter_subset_left
  have hRr : range R.chart ⊆ range L.chart := by
    rw [R.range_chart, L.range_chart]
    exact hRL
  have hRJ := (image_mono hRr).trans hLJ
  have hComm := q.fullRecognitionPairs.restriction_comm R L J J hRr (Subset.rfl) hRJ hLJ
  rw [B.fullRecognitionPresentation.atlas.restriction_id J _, BoundedAlgHom.comp_id] at hComm
  obtain ⟨hrF, hrE⟩ := A.atlas.compactOpenChartPiece_restriction L hE hc hRL
  have hg : (q.fullRecognitionPairs.pullback R J hRJ).IsFiniteBanach ∧
      (q.fullRecognitionPairs.pullback R J hRJ).AlgebraicallyFiniteEtale := by
    rw [← hComm]
    exact ⟨hrF.comp hqL.1, hrE.comp hqL.2⟩
  refine ⟨R, hRP, hRJ, hg.1, hg.2, ?_⟩
  intro t
  have ht : J.chart t ∈ J.locus := J.range_chart ▸ mem_range_self t
  obtain ⟨y, hy, hyq⟩ := hJE ht
  have hyR : y ∈ range R.chart := by
    rw [R.range_chart, hR]
    refine ⟨hy, ?_⟩
    change q.baseMap y ∈ J.locus
    rwa [hyq]
  obtain ⟨s, hs⟩ := hyR
  exact ⟨s, J.isEmbedding_chart.injective
    ((q.fullRecognitionPairs.chart_comm R J hRJ s).trans ((congrArg q.baseMap hs).trans hyq))⟩

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation

variable {A B : SaturatedAtlasPresentation.{u, u, u} K}

set_option backward.isDefEq.respectTransparency false in
/-- A small chart lying over exactly the preimage of a target chart in a domain
is the categorical pullback, with the specified chart map. -/
theorem isPullback_localizedSmallChart_of_domainPreimage
    (E : A.AnalyticDomain) (P : A.presentation.atlas.Index) (W : B.presentation.atlas.Index)
    (F : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (r : localizationFunctor.obj (A.smallChartSpectrum P) ⟶ localizationFunctor.obj (A.domain E))
    (b : localizationFunctor.obj (A.smallChartSpectrum P) ⟶ localizationFunctor.obj (B.smallChartSpectrum W))
    (hr : r ≫ A.localizedDomainInclusion E = A.localizedSmallChart P)
    (hb : A.localizedSmallChart P ≫ F = b ≫ B.localizedSmallChart W)
    (hpre : range (A.presentation.atlas.chart P) = E.carrier ∩
      (localizedSpaceFunctor.map F) ⁻¹' range (B.presentation.atlas.chart W)) :
    IsPullback r b (A.localizedDomainInclusion E ≫ F) (B.localizedSmallChart W) := by
  let i := A.localizedDomainInclusion E
  let j := B.localizedSmallChart W
  have hComm : r ≫ i ≫ F = b ≫ j :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ F) hr).trans hb)
  have hLift (c : PullbackCone (i ≫ F) j) :
      ∃ l : c.pt ⟶ localizationFunctor.obj (A.smallChartSpectrum P),
        l ≫ r = c.fst ∧ l ≫ b = c.snd := by
    obtain ⟨l, hl⟩ := A.exists_factor_localizedSmallChart (c.fst ≫ i) P (fun z => by
      rw [hpre]
      refine ⟨?_, ?_⟩
      · change localizedSpaceFunctor.map (c.fst ≫ A.localizedDomainInclusion E) z ∈ E.carrier
        rw [Functor.map_comp, TopCat.comp_app, A.localizedSpaceFunctor_map_localizedDomainInclusion]
        exact (localizedSpaceFunctor.map c.fst z).property
      · have hz := congrArg (fun t => localizedSpaceFunctor.map t z) c.condition
        simp only [Functor.map_comp, TopCat.comp_app] at hz
        change localizedSpaceFunctor.map F (localizedSpaceFunctor.map (c.fst ≫ i) z) ∈
          range (B.presentation.atlas.chart W)
        rw [Functor.map_comp, TopCat.comp_app, hz, ← B.localizedSmallChart_range W]
        exact mem_range_self _)
    have hli : l ≫ r = c.fst := (cancel_mono i).mp
      ((Category.assoc _ _ _).trans ((congrArg (l ≫ ·) hr).trans hl))
    refine ⟨l, hli, (cancel_mono j).mp ?_⟩
    calc
      (l ≫ b) ≫ j = (l ≫ r) ≫ i ≫ F := by simp only [Category.assoc, hComm]
      _ = c.fst ≫ i ≫ F := congrArg (· ≫ i ≫ F) hli
      _ = c.snd ≫ j := c.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hComm
    (fun c => (hLift c).choose) (fun c => (hLift c).choose_spec.1)
    (fun c => (hLift c).choose_spec.2) (fun c m hm _ => by
      apply (cancel_mono (A.localizedSmallChart P)).mp
      rw [← hr, ← Category.assoc, ← Category.assoc, hm, (hLift c).choose_spec.1]))

end SaturatedAtlasPresentation

end Langlands.Analytic

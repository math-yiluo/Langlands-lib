import Langlands.Geometry.Analytic.FiniteEtaleOverRecognition
import Langlands.Geometry.Analytic.FiniteEtaleSourcePieces

/-! # Étale descent on recognized open neighborhoods -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {q : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {f : StrongHom B.saturatedPresentation C.saturatedPresentation}

private theorem finiteEtale_restriction_of_openCut
    (P Q : A.atlas.saturatedAtlas.RecognizedSubset) {E : Set A.space}
    (hE : IsOpen E) (hPQ : P.locus = Q.locus ∩ E) (hsub : P.locus ⊆ Q.locus) :
    (P.restriction Q hsub).IsFiniteBanach ∧
      (P.restriction Q hsub).AlgebraicallyFiniteEtale := by
  have hcl := P.isClopen_chart_preimage_of_eq_inter Q hE hPQ
  have hd : Represents K (clopenRationalChart _ hcl).baseMap (Q.chart ⁻¹' P.locus) := by
    have h : Represents K (clopenRationalChart _ hcl).baseMap
        (clopenRationalChart _ hcl).locus := (clopenRationalChart _ hcl).toDomain.represents
    rwa [locus_clopenRationalChart] at h
  obtain ⟨M, hM, hlift⟩ := exists_lift_clopenRationalChart _ hcl
  obtain ⟨N, hN, hlift'⟩ :=
    hd.exists_lift_of_exists_lift (P.restriction_represents Q hsub) hM hlift
  have hfin := (P.restriction Q hsub).isFiniteBanach_of_lift hN hlift'
  exact ⟨hfin, (P.restriction Q hsub).algebraicallyFiniteEtale_of_isEtaleAtPoint hfin.finite
    (P.restriction_isEtaleAtPoint Q hsub hcl)⟩

/-- Let the cover and the composite have aligned finite étale neighborhoods.
On each recognized target piece, recognition of the image of the composite
piece suffices to make the descended neighborhood finite étale. -/
theorem IsFiniteEtaleOver.of_comp_of_recognizedImages
    {D E : Set A.space} {U : Set B.space} {T : Set C.space}
    (hq : q.IsFiniteEtaleOver D U) (hE : IsOpen E) (hED : E ⊆ D)
    (hc : (q.saturatedComp f A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteEtaleOver E T)
    (hRecognize : ∀ W : C.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ T →
      ∃ H : B.atlas.saturatedAtlas.RecognizedSubset,
        H.locus = q.baseMap '' E ∩ f.baseMap ⁻¹' W.locus) :
    f.IsFiniteEtaleOver (q.baseMap '' E) T := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact hc.1 ⟨y, hy, rfl⟩
  intro W hWT
  obtain ⟨P, hPW, hP, hPc⟩ := hc.2 W hWT
  obtain ⟨H, hH⟩ := hRecognize W hWT
  have hHU : H.locus ⊆ U := by
    rw [hH]
    rintro _ ⟨⟨y, hy, rfl⟩, -⟩
    exact hq.1 ⟨y, hED hy, rfl⟩
  obtain ⟨Q, hQH, hQ, hQq⟩ := hq.2 H hHU
  have hPQ : P.locus = Q.locus ∩ E := by
    rw [hP, hQ, hH]
    ext y
    constructor
    · rintro ⟨hy, hWy⟩
      exact ⟨⟨hED hy, ⟨y, hy, rfl⟩, hWy⟩, hy⟩
    · rintro ⟨⟨-, -, hWy⟩, hy⟩
      exact ⟨hy, hWy⟩
  have hsub : P.locus ⊆ Q.locus := hPQ.trans_subset inter_subset_left
  have hPr : range P.chart ⊆ range Q.chart := by
    rw [P.range_chart, Q.range_chart]
    exact hsub
  have hPH : q.baseMap '' range P.chart ⊆ range H.chart :=
    (image_mono hPr).trans hQH
  have hHW : f.baseMap '' range H.chart ⊆ range W.chart := by
    rintro _ ⟨x, hx, rfl⟩
    have hxH : x ∈ H.locus := H.range_chart ▸ hx
    rw [hH] at hxH
    exact W.range_chart.symm ▸ hxH.2
  have hComm := q.fullRecognitionPairs.restriction_comm P Q H H hPr
    (Subset.refl _) hPH hQH
  rw [B.fullRecognitionPresentation.atlas.restriction_id H (Subset.refl _),
    BoundedAlgHom.comp_id] at hComm
  have hPq : (q.fullRecognitionPairs.pullback P H hPH).IsFiniteBanach ∧
      (q.fullRecognitionPairs.pullback P H hPH).AlgebraicallyFiniteEtale := by
    rw [← hComm]
    obtain ⟨hFin, hEt⟩ := finiteEtale_restriction_of_openCut P Q hE hPQ hsub
    exact ⟨hFin.comp hQq.1, hEt.comp hQq.2⟩
  have hSurj : Function.Surjective
      (BanachSpectrum.comap (q.fullRecognitionPairs.pullback P H hPH).toBoundedRingHom) := by
    intro t
    have ht : H.chart t ∈ H.locus := H.range_chart ▸ mem_range_self t
    rw [hH] at ht
    obtain ⟨⟨y, hy, hyq⟩, hWy⟩ := ht
    have hyP : y ∈ range P.chart := by
      rw [P.range_chart, hP]
      refine ⟨hy, ?_⟩
      change f.baseMap (q.baseMap y) ∈ W.locus
      rw [hyq]
      exact hWy
    obtain ⟨s, hs⟩ := hyP
    refine ⟨s, H.isEmbedding_chart.injective ?_⟩
    exact (q.fullRecognitionPairs.chart_comm P H hPH s).trans
      ((congrArg q.baseMap hs).trans hyq)
  refine ⟨H, hHW, hH, ?_⟩
  rw [fullRecognitionPairs_comp q f P H W hPH hHW hPW] at hPc
  exact BoundedAlgHom.finiteBanach_etale_of_finiteEtale_comp hPq hSurj hPc

/-- Open finite étale neighborhoods of a cover and of its composite at a
given lift, with the composite's source inside the cover's source. -/
structure FiniteEtaleSourceNeighborhoods
    (q : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (f : StrongHom B.saturatedPresentation C.saturatedPresentation) (y : A.space) where
  coverSource : Set A.space
  coverTarget : Set B.space
  compSource : Set A.space
  compTarget : Set C.space
  isOpen_coverSource : IsOpen coverSource
  isOpen_coverTarget : IsOpen coverTarget
  isOpen_compSource : IsOpen compSource
  isOpen_compTarget : IsOpen compTarget
  mem_compSource : y ∈ compSource
  compSource_subset : compSource ⊆ coverSource
  cover_finiteEtale : q.IsFiniteEtaleOver coverSource coverTarget
  comp_finiteEtale : (q.saturatedComp f A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteEtaleOver compSource compTarget

/-- Choose aligned neighborhoods using local finiteness and shrinking. -/
def finiteEtaleSourceNeighborhoods
    (hq : q.IsEtaleAllPieces)
    (hc : (q.saturatedComp f A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAllPieces)
    (y : A.space) : FiniteEtaleSourceNeighborhoods q f y := by
  apply Classical.choice
  obtain ⟨D, U, hD, hU, hyD, hqfin⟩ := strongEtaleLocallyFiniteEtale A B q hq y
  obtain ⟨E₀, T₀, hE₀, hT₀, hy₀, hcfin⟩ :=
    (strongEtaleLocallyFiniteEtale A C _ hc y).isFiniteAt
  obtain ⟨E, T, hE, hT, hyE, hED, -, -, hfin⟩ :=
    hcfin.exists_small hE₀ hT₀ hy₀ (hD.mem_nhds hyD)
  exact ⟨⟨D, U, E, T, hD, hU, hE, hT, hyE, hED, hqfin, hc.isFiniteEtaleOver hE hfin⟩⟩

/-- If the images of the composite's pieces in the aligned neighborhoods
are recognized, the descended map is étale at the covered point. -/
theorem FiniteEtaleSourceNeighborhoods.isEtaleAtAllPieces
    {y : A.space} (N : FiniteEtaleSourceNeighborhoods q f y) (hq : q.IsEtaleAllPieces)
    (hRecognize : ∀ W : C.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ N.compTarget →
      ∃ H : B.atlas.saturatedAtlas.RecognizedSubset,
        H.locus = q.baseMap '' N.compSource ∩ f.baseMap ⁻¹' W.locus) :
    f.IsEtaleAtAllPieces (q.baseMap y) := by
  have hf := N.cover_finiteEtale.of_comp_of_recognizedImages
    N.isOpen_compSource N.compSource_subset N.comp_finiteEtale hRecognize
  exact IsLocallyFiniteEtaleAt.isEtaleAtAllPieces
    ⟨q.baseMap '' N.compSource, N.compTarget, hq.isOpenMap _ N.isOpen_compSource,
      N.isOpen_compTarget, ⟨y, N.mem_compSource, rfl⟩, hf⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

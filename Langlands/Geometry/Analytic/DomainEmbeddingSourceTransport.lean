import Langlands.Geometry.Analytic.DomainEmbeddingRecognition
import Langlands.Geometry.Analytic.QuasiIsoSourceEtale

/-! # Source transport through full open domain embeddings -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Topology Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

namespace IsDomainEmbedding

variable {f : StrongHom A B}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  (hf : f.IsDomainEmbedding) (hc : f.HasCoherentPullbacks)


/-- The image has exactly the source recognized locus after the ambient embedding. -/
theorem recognizedImage_admissible (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    f.baseMap '' Set.range V.chart ⊆ Set.range (hf.recognizedImage hc V).chart := by
  rw [V.range_chart, (hf.recognizedImage hc V).range_chart,
    hf.recognizedImage_locus hc]

include hf hc in
/-- Finiteness over a neighborhood descends along a full source
domain embedding, with the source neighborhood transported by its image. -/
theorem IsFiniteOver.of_precomp_domainEmbedding
    {V : Set A.space} {U : Set C.space}
    (hfg : ((f.saturationExtension hc).saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteOver V U) :
    g.IsFiniteOver (f.baseMap '' V) U := by
  refine ⟨?_, fun Z hZ => ?_⟩
  · rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact hfg.1 ⟨x, hx, rfl⟩
  · obtain ⟨P, hPZ, hP, hfin⟩ := hfg.2 Z hZ
    let Y := hf.recognizedImage hc P
    let e := (hf.recognizedImageEquiv hc P).symm
    have hPY := hf.recognizedImage_admissible hc P
    have hY : Y.locus = (f.baseMap '' V) ∩ g.baseMap ⁻¹' Z.locus := by
      rw [hf.recognizedImage_locus hc, hP]
      exact IsQuasiIso.image_inter_comp_preimage (f := f.saturationExtension hc) g V Z.locus
    have hYZ : g.baseMap '' Set.range Y.chart ⊆ Set.range Z.chart := by
      change g.originalRestriction.baseMap '' Set.range Y.chart ⊆ Set.range Z.chart
      rw [Y.range_chart, Z.range_chart]
      rintro _ ⟨y, hy, rfl⟩
      exact (hY ▸ hy).2
    refine ⟨Y, hYZ, hY, ?_⟩
    have heq : e.symm.toBoundedAlgHom.comp
        (((f.saturationExtension hc).saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
          B.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionPairs.pullback
            P Z hPZ) = g.fullRecognitionPairs.pullback Y Z hYZ := by
      rw [fullRecognitionPairs_comp (f.saturationExtension hc) g P Y Z hPY hYZ hPZ]
      rw [hf.saturationExtension_fullRecognitionPairs_pullback_recognizedImage hc P hPY]
      apply BoundedAlgHom.ext
      intro z
      exact e.symm_apply_apply _
    exact heq ▸ e.symm.isFiniteBanach.comp hfin

variable (ho : IsOpenEmbedding f.baseMap)

include hf hc ho in
/-- Pointwise conditions on every finite piece descend through a source
domain embedding when they compose and hold for bounded equivalences. -/
theorem HasAllPiecesAt.of_precomp_domainEmbedding
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄,
      BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hcomp : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄ (a : BoundedAlgHom K S T)
      (b : BoundedAlgHom K R S) (t : BanachSpectrum T),
      a.toAlgHom.toRingHom.FiniteType → b.toAlgHom.toRingHom.FiniteType →
        Q a t → Q b (BanachSpectrum.comap a.toBoundedRingHom t) → Q (a.comp b) t)
    (he : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄ (e : BoundedAlgEquiv K R S)
      (t : BanachSpectrum S), Q e.toBoundedAlgHom t)
    {x : A.space}
    (hfg : ((f.saturationExtension hc).saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).HasAllPiecesAt Q x) :
    g.HasAllPiecesAt Q (f.baseMap x) := by
  obtain ⟨V, U, hV, hU, hx, hfin, hQ⟩ := hfg
  refine ⟨f.baseMap '' V, U, ho.isOpenMap V hV, hU, ⟨x, hx, rfl⟩,
    IsFiniteOver.of_precomp_domainEmbedding hf hc hfin, ?_⟩
  intro Z hZ hxZ W hWZ hW t ht
  obtain ⟨P, hPZ, hP, hPfin⟩ := hfin.2 Z hZ
  let Y := hf.recognizedImage hc P
  let e := (hf.recognizedImageEquiv hc P).symm
  have hPY := hf.recognizedImage_admissible hc P
  have hY : Y.locus = (f.baseMap '' V) ∩ g.baseMap ⁻¹' Z.locus := by
    rw [hf.recognizedImage_locus hc, hP]
    exact IsQuasiIso.image_inter_comp_preimage (f := f.saturationExtension hc) g V Z.locus
  have hWY : W = Y := by
    apply Subtype.ext
    apply Subtype.ext
    change W.locus = Y.locus
    exact hW.trans hY.symm
  subst W
  have heq : e.symm.toBoundedAlgHom.comp
      (((f.saturationExtension hc).saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionPairs.pullback
          P Z hPZ) = g.fullRecognitionPairs.pullback Y Z hWZ := by
    rw [fullRecognitionPairs_comp (f.saturationExtension hc) g P Y Z hPY hWZ hPZ]
    rw [hf.saturationExtension_fullRecognitionPairs_pullback_recognizedImage hc P hPY]
    apply BoundedAlgHom.ext
    intro z
    exact e.symm_apply_apply _
  let s := e.spectrumHomeomorph.symm t
  have hst : BanachSpectrum.comap
      ((f.saturationExtension hc).fullRecognitionPairs.pullback P Y hPY).toBoundedRingHom s = t := by
    rw [hf.saturationExtension_fullRecognitionPairs_pullback_recognizedImage hc P hPY]
    change e.spectrumHomeomorph (e.spectrumHomeomorph.symm t) = t
    exact e.spectrumHomeomorph.apply_symm_apply t
  have hs : P.chart s = x := by
    apply hf.1.injective
    exact ((f.saturationExtension hc).fullRecognitionPairs.chart_comm P Y hPY s).symm.trans
      ((congrArg Y.chart hst).trans ht)
  have hQt := hQ Z hZ hxZ P hPZ hP s hs
  have hres := hcomp e.symm.toBoundedAlgHom _ t
    e.symm.isFiniteBanach.finite.finiteType hPfin.finite.finiteType (he e.symm t) hQt
  exact (congrArg (fun q => Q q t) heq).mp hres

include hf hc ho in
/-- Flatness over all pieces descends along a source open domain embedding. -/
theorem IsFlatAtAllPieces.of_precomp_domainEmbedding {x : A.space}
    (hfg : ((f.saturationExtension hc).saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFlatAtAllPieces x) :
    g.IsFlatAtAllPieces (f.baseMap x) :=
  HasAllPiecesAt.of_precomp_domainEmbedding hf hc ho
    (Q := fun _ _ a t => a.IsFlatAtPoint t)
    (fun _ _ _ _ _ _ _ _ ha hb => ha.comp hb)
    (fun _ _ e t => ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
      e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint t).1) hfg

include hf hc ho in
/-- Unramifiedness over all pieces descends along a source open domain embedding. -/
theorem IsUnramifiedAtAllPieces.of_precomp_domainEmbedding {x : A.space}
    (hfg : ((f.saturationExtension hc).saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsUnramifiedAtAllPieces x) :
    g.IsUnramifiedAtAllPieces (f.baseMap x) :=
  HasAllPiecesAt.of_precomp_domainEmbedding hf hc ho
    (Q := fun _ _ a t => a.IsUnramifiedAtPoint t)
    (fun _ _ _ _ _ _ ha hb hQa hQb => BoundedAlgHom.IsUnramifiedAtPoint.comp ha hb hQa hQb)
    (fun _ _ e t => ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
      e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint t).2) hfg

include hf hc ho in
/-- An étale neighborhood descends to the open source image. -/
theorem IsEtaleAtAllPieces.of_precomp_domainEmbedding {x : A.space}
    (hfg : ((f.saturationExtension hc).saturatedComp g A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAtAllPieces x) :
    g.IsEtaleAtAllPieces (f.baseMap x) := by
  obtain ⟨V, hV, hx, hQ⟩ := hfg
  refine ⟨f.baseMap '' V, ho.isOpenMap V hV, ⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨IsUnramifiedAtAllPieces.of_precomp_domainEmbedding hf hc ho (hQ a ha).1,
    IsFlatAtAllPieces.of_precomp_domainEmbedding hf hc ho (hQ a ha).2⟩

end IsDomainEmbedding
end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

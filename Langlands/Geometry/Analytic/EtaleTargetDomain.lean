import Langlands.Geometry.Analytic.EtaleDomainTargetCancellation
import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality
import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # Étaleness after factoring through an analytic domain -/

noncomputable section

universe u v

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  {f : StrongHom A.saturatedPresentation B.saturatedPresentation} {g : StrongHom B C}

set_option backward.isDefEq.respectTransparency false in
private theorem hasAllPiecesAt_of_comp_domainEmbedding
    (hg : g.IsDomainEmbedding) (hc : g.HasCoherentPullbacks)
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄,
      BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hcomp : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (a : BoundedAlgHom K S T) (e : BoundedAlgEquiv K R S) (t : BanachSpectrum T),
      a.IsFiniteBanach → Q a t → Q (a.comp e.toBoundedAlgHom) t)
    {x : A.space}
    (hx : (f.saturatedComp (g.saturationExtension hc) A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).HasAllPiecesAt Q x) :
    f.HasAllPiecesAt Q x := by
  let g' := g.saturationExtension hc
  let fg := f.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains
  change fg.HasAllPiecesAt Q x at hx
  obtain ⟨V, U, hV, hU, hxV, hfin, hQ⟩ := hx
  have pieces (W : B.atlas.saturatedAtlas.RecognizedSubset) (hW : W.locus ⊆ g.baseMap ⁻¹' U) :
      ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
        (hPW : f.baseMap '' Set.range P.chart ⊆ Set.range W.chart),
        P.locus = V ∩ f.baseMap ⁻¹' W.locus ∧
        (f.fullRecognitionPairs.pullback P W hPW).IsFiniteBanach ∧
        (f.baseMap x ∈ W.locus → ∀ t : BanachSpectrum P.algebra, P.chart t = x →
          Q (f.fullRecognitionPairs.pullback P W hPW) t) := by
    let Z := hg.recognizedImage hc W
    let e := hg.recognizedImageEquiv hc W
    have hWZ := hg.recognizedImage_admissible hc W
    have hZ : Z.locus ⊆ U := by
      rw [hg.recognizedImage_locus]
      exact Set.image_subset_iff.mpr hW
    obtain ⟨P, hPZ, hP, hPfin⟩ := hfin.2 Z hZ
    have hpre : fg.baseMap ⁻¹' Z.locus = f.baseMap ⁻¹' W.locus := by
      rw [hg.recognizedImage_locus]
      change f.baseMap ⁻¹' (g.baseMap ⁻¹' (g.baseMap '' W.locus)) = _
      rw [Set.preimage_image_eq _ hg.1.injective]
    have hPl : P.locus = V ∩ f.baseMap ⁻¹' W.locus := by rwa [hpre] at hP
    have hPW : f.baseMap '' Set.range P.chart ⊆ Set.range W.chart := by
      change f.originalRestriction.baseMap '' Set.range P.chart ⊆ Set.range W.chart
      rw [P.range_chart, W.range_chart, hPl]
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    have heq : (fg.fullRecognitionPairs.pullback P Z hPZ).comp e.toBoundedAlgHom =
        f.fullRecognitionPairs.pullback P W hPW := by
      change ((f.saturatedComp g' _ _).fullRecognitionPairs.pullback P Z hPZ).comp
        e.toBoundedAlgHom = _
      rw [fullRecognitionPairs_comp f g' P W Z hPW hWZ hPZ,
        hg.saturationExtension_fullRecognitionPairs_pullback_recognizedImage hc W hWZ]
      apply BoundedAlgHom.ext
      intro z
      exact congrArg (f.fullRecognitionPairs.pullback P W hPW) (e.symm_apply_apply z)
    refine ⟨P, hPW, hPl, heq ▸ hPfin.comp e.isFiniteBanach, fun hxW t ht => ?_⟩
    have hxZ : fg.baseMap x ∈ Z.locus := by
      rw [hg.recognizedImage_locus]
      exact ⟨f.baseMap x, hxW, rfl⟩
    exact (congrArg (fun a => Q a t) heq).mp
      (hcomp _ e t hPfin (hQ Z hZ hxZ P hPZ hP t ht))
  refine ⟨V, g.baseMap ⁻¹' U, hV, hU.preimage g.baseMap.continuous, hxV, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hfin.1 ⟨y, hy, rfl⟩
  · intro W hW
    obtain ⟨P, hPW, hP, hPfin, -⟩ := pieces W hW
    exact ⟨P, hPW, hP, hPfin⟩
  · intro W hW hxW P hPW hP t ht
    obtain ⟨P', _, hP', _, hP'Q⟩ := pieces W hW
    have h : P' = P := Subtype.ext (Subtype.ext (hP'.trans hP.symm))
    subst P'
    exact hP'Q hxW t ht

/-- Étaleness over all pieces descends through an analytic domain embedding on
the target. -/
private theorem isEtaleAllPieces_of_comp_domainEmbedding
    (hg : g.IsDomainEmbedding) (hc : g.HasCoherentPullbacks)
    (hfg : (f.saturatedComp (g.saturationExtension hc) A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAllPieces) : f.IsEtaleAllPieces := by
  intro x
  obtain ⟨V, hV, hx, h⟩ := hfg x
  refine ⟨V, hV, hx, fun y hy => ⟨?_, ?_⟩⟩
  · apply hasAllPiecesAt_of_comp_domainEmbedding hg hc
      (Q := fun _ _ a t => a.IsUnramifiedAtPoint t) _ (h y hy).1
    intro R S T a e t ha hut
    exact BoundedAlgHom.IsUnramifiedAtPoint.comp ha.finite.finiteType
      e.isFiniteBanach.finite.finiteType hut
      ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
        e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint _).2
  · apply hasAllPiecesAt_of_comp_domainEmbedding hg hc
      (Q := fun _ _ a t => a.IsFlatAtPoint t) _ (h y hy).2
    intro R S T a e t _ hft
    exact hft.comp ((BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
      e.toBoundedAlgHom e.toAlgEquiv.bijective).isEtaleAtPoint _).1

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation

variable {A B : SaturatedAtlasPresentation.{u, v, v} K}

/-- Étaleness descends through a canonical analytic domain inclusion on the target. -/
def EtaleTargetDomainStatement : Prop :=
  ∀ {X Y : LocalizedCategory.{u, v, v} (K := K)}
    (D : (presentationOf Y).AnalyticDomain) (f : X ⟶ domainObj Y D),
    etale (f ≫ domainι Y D) → etale f

theorem etaleTargetDomain : EtaleTargetDomainStatement.{u, v} (K := K) :=
  fun D f hf => etale_of_comp_domainι D (f := f) hf

end SaturatedAtlasPresentation
end Langlands.Analytic

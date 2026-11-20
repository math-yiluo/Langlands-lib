import Langlands.Geometry.Analytic.StrongEtaleSourceOpenLocality
import Langlands.Geometry.Analytic.FullRecognitionAllPiecesRestriction
import Langlands.Geometry.Analytic.LocalizedEtaleComposition

/-! # Étale cancellation along analytic domain inclusions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsDomainEmbedding

open CategoryTheory Set IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {j : StrongHom B C} (hj : j.IsDomainEmbedding) (hc : j.HasCoherentPullbacks)

local notation "c" => (g.saturatedComp (j.saturationExtension hc)
  A.atlas.saturatedAtlas_hasAllLocalDomains B.atlas.saturatedAtlas_hasAllLocalDomains)

include hj hc in
private theorem preimage_recognizedImage (W : B.atlas.saturatedAtlas.RecognizedSubset) :
    (c).baseMap ⁻¹' (hj.recognizedImage hc W).locus = g.baseMap ⁻¹' W.locus := by
  rw [hj.recognizedImage_locus hc]
  exact congrArg (fun s : Set B.space => g.baseMap ⁻¹' s)
    (Set.preimage_image_eq W.locus hj.1.injective)

include hj hc in
private theorem pullback_comp_recognizedImageEquiv
    (P : A.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart)
    (hcP : (c).baseMap '' Set.range P.chart ⊆ Set.range (hj.recognizedImage hc W).chart) :
    ((c).fullRecognitionPairs.pullback P (hj.recognizedImage hc W) hcP).comp
        (hj.recognizedImageEquiv hc W).toBoundedAlgHom =
      g.fullRecognitionPairs.pullback P W h := by
  rw [fullRecognitionPairs_comp g (j.saturationExtension hc) P W
    (hj.recognizedImage hc W) h (hj.recognizedImage_admissible hc W) hcP,
    hj.saturationExtension_fullRecognitionPairs_pullback_recognizedImage
      hc W (hj.recognizedImage_admissible hc W)]
  apply BoundedAlgHom.ext
  intro z
  exact congrArg (g.fullRecognitionPairs.pullback P W h)
    ((hj.recognizedImageEquiv hc W).symm_apply_apply z)

include hj hc in
/-- A finite chart decomposition over the ambient target remains finite
over its inverse image in a fully represented target domain. -/
theorem isFiniteOver_of_postcomp_domainEmbedding
    {V : Set A.space} {U : Set C.space}
    (hfin : (c).IsFiniteOver V U) :
    g.IsFiniteOver V (j.baseMap ⁻¹' U) := by
  refine ⟨?_, fun W hW => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hfin.1 ⟨x, hx, rfl⟩
  · let Z := hj.recognizedImage hc W
    have hZ : Z.locus ⊆ U := by
      rw [hj.recognizedImage_locus hc]
      exact Set.image_subset_iff.mpr hW
    obtain ⟨P, hPZ, hP, hPfin⟩ := hfin.2 Z hZ
    have hPl : P.locus = V ∩ g.baseMap ⁻¹' W.locus :=
      hP.trans (congrArg (V ∩ ·) (preimage_recognizedImage (g := g) hj hc W))
    have hPW : g.baseMap '' Set.range P.chart ⊆ Set.range W.chart := by
      change g.originalRestriction.baseMap '' Set.range P.chart ⊆ Set.range W.chart
      rw [P.range_chart, W.range_chart, hPl]
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    refine ⟨P, hPW, hPl, ?_⟩
    rw [← pullback_comp_recognizedImageEquiv hj hc P W hPW hPZ]
    exact hPfin.comp (hj.recognizedImageEquiv hc W).isFiniteBanach

include hj hc in
/-- Étaleness on the ambient finite pieces gives étaleness on the same
pieces with the target algebra identified by the domain embedding. -/
theorem hasAllPiecesAt_etale_of_postcomp_domainEmbedding {x : A.space}
    (hx : (c).HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) x) :
    g.HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) x := by
  obtain ⟨V, U, hV, hU, hxV, hfin, hQ⟩ := hx
  refine ⟨V, j.baseMap ⁻¹' U, hV, hU.preimage j.baseMap.continuous, hxV,
    isFiniteOver_of_postcomp_domainEmbedding hj hc hfin, ?_⟩
  intro W hW hxW P hPW hPl s hs
  let Z := hj.recognizedImage hc W
  have hZ : Z.locus ⊆ U := by
    rw [hj.recognizedImage_locus hc]
    exact Set.image_subset_iff.mpr hW
  have hxZ : (c).baseMap x ∈ Z.locus := by
    rw [hj.recognizedImage_locus hc]
    exact ⟨g.baseMap x, hxW, rfl⟩
  obtain ⟨P', hP'Z, hP'l, hP'fin⟩ := hfin.2 Z hZ
  have hP'l' : P'.locus = V ∩ g.baseMap ⁻¹' W.locus :=
    hP'l.trans (congrArg (V ∩ ·) (preimage_recognizedImage (g := g) hj hc W))
  have hPP : P' = P := Subtype.ext (Subtype.ext (hP'l'.trans hPl.symm))
  subst P'
  let e := hj.recognizedImageEquiv hc W
  have he : e.toBoundedAlgHom.AlgebraicallyFiniteEtale :=
    BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective _ e.bijective
  rw [← pullback_comp_recognizedImageEquiv hj hc P W hPW hP'Z]
  exact (hQ Z hZ hxZ P hP'Z hP'l s hs).comp hP'fin.finite.finiteType
    e.isFiniteBanach.finite.finiteType (he.isEtaleAtPoint _)

include hj hc in
/-- Étaleness cancels on the right along a full target domain embedding. -/
theorem isEtaleAllPieces_of_postcomp_domainEmbedding
    (he : (c).IsEtaleAllPieces) : g.IsEtaleAllPieces := by
  intro x
  obtain ⟨V, hV, hx, hQ⟩ := he x
  refine ⟨V, hV, hx, fun y hy => ?_⟩
  exact hasAllPiecesAt_isEtaleAtPoint_iff.mp
    (hasAllPiecesAt_etale_of_postcomp_domainEmbedding hj hc
      (hasAllPiecesAt_isEtaleAtPoint_iff.mpr (hQ y hy)))

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsDomainEmbedding

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Strong étaleness can be tested after composing with the inclusion of
the target analytic domain. -/
theorem strongEtale_of_comp_domainInclusion
    {A B : SaturatedAtlasPresentation.{u, v, w} K} (D : B.AnalyticDomain)
    {f : A ⟶ B.domain D} (hf : strongEtale (f ≫ B.domainInclusion D)) :
    strongEtale f := by
  unfold strongEtale at hf ⊢
  rw [Functor.map_comp] at hf
  exact StrongHom.IsDomainEmbedding.isEtaleAllPieces_of_postcomp_domainEmbedding
    (domainInclusion_isDomainEmbedding B D)
    ((B.domainInclusion D).hasCoherentPullbacks_of_saturated (B.domain D).hasAllLocalDomains)
    hf

set_option backward.isDefEq.respectTransparency false in
/-- Étaleness of the composite with an analytic domain inclusion implies
étaleness of the original localized map into the domain. -/
theorem etale_of_comp_domainι
    {X Y : LocalizedCategory.{u, v, v} (K := K)} (D : (presentationOf Y).AnalyticDomain)
    {f : X ⟶ domainObj Y D} (hf : etale (f ≫ domainι Y D)) :
    etale f := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  obtain ⟨B, rfl⟩ := localizedObjectEquiv.surjective Y
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  have hf' := etale_comp (etale_of_isIso (localizedQuasiIso φ.s φ.hs).hom) hf
  change etale (localizationFunctor.map φ.s ≫ localizedRightFraction φ ≫
    localizationFunctor.map (B.domainInclusion D)) at hf'
  rw [← Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction,
    ← Functor.map_comp] at hf'
  exact etale_localizedRightFraction_of_strongEtale φ
    (strongEtale_of_comp_domainInclusion D
      ((etale_localizationFunctor_map_iff_strongEtale _).mp hf'))

/-- The existing unique lift of an étale arrow into a domain containing
its image is étale. It carries its original factorization equation. -/
def etaleDomainLift
    {X Y : LocalizedCategory.{u, v, v} (K := K)} (D : (presentationOf Y).AnalyticDomain)
    (f : X ⟶ Y) (hf : etale f) (hD : ∀ x, localizedSpaceFunctor.map f x ∈ D.carrier) :
    {g : X ⟶ domainObj Y D // etale g ∧ g ≫ domainι Y D = f} := by
  refine ⟨domainLift D f hD, ?_, domainLift_comp D f hD⟩
  exact etale_of_comp_domainι D ((domainLift_comp D f hD).symm ▸ hf)

end Langlands.Analytic.SaturatedAtlasPresentation

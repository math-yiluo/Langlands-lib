import Langlands.Geometry.Analytic.SmallCommonEtaleProduct
import Langlands.Geometry.Analytic.LocalizedEtalePullbackExistence

/-! # Étale structure maps of products of localized étale morphisms -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory CategoryTheory.Limits PresentedAffinoidAlgebra AffinoidAtlasPresentation
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

set_option maxHeartbeats 900000 in
private theorem recognizedLocalizedPullback_common_etale
    {A B X : SaturatedAtlasPresentation.{u, v, v} K}
    (f : A ⟶ X) (g : B ⟶ X) (hf : strongEtale f) (hg : strongEtale g) :
    etale ((recognizedLocalizedPullback f g AffinoidPushout.finiteBanachPushout hf).1.snd ≫
      localizationFunctor.map g) := by
  let hpush : AffinoidPushout.FiniteBanachPushoutStatement K := AffinoidPushout.finiteBanachPushout
  let _ := recognition_fibreProductSpace_small f g hpush hf
  let F := (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f
  let G := (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map g
  let _ : Small.{v} (FibreProduct.chartSystem F.compatibleRecognitionMap G.compatibleRecognitionMap).Space :=
    recognition_fibreProductSpace_small f g hpush hf
  let rf := recognitionMap f
  let rg := recognitionMap g
  let T := smallFibreProduct rf rg
  let D := recognitionBase X
  let B₀ := recognitionSource g
  let r : T ⟶ ofSaturation B₀.presentation := (recognitionSmallSnd F G).saturationExtension
  let k : ofSaturation B₀.presentation ⟶ ofSaturation D.presentation :=
    G.compatibleRecognitionMap.saturationExtension
  have hk : k.IsEtaleAllPieces := (recognitionMap_strongEtale_iff g).mpr hg
  have hall : (recognitionSmallCommon F G).IsEtaleAllPieces :=
    recognitionSmallCommon_isEtaleAllPieces F G hf hk
  have hstr : strongEtale (r ≫ k) := (strongEtale_ofSaturation_iff (r ≫ k)).mpr hall
  have he : B₀.saturationIso.hom ≫ rg = k ≫ D.saturationIso.hom :=
    ((saturationComparisonNatIso (K := K)).hom.naturality rg).symm
  have hs : smallFibreProductSnd rf rg ≫ rg = (r ≫ k) ≫ D.saturationIso.hom := by
    change (r ≫ B₀.saturationIso.hom) ≫ rg = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (r ≫ ·) he).trans (Category.assoc _ _ _).symm)
  have hsmall : strongEtale (smallFibreProductSnd rf rg ≫ rg) := by
    rw [hs]
    exact strongEtale_comp hstr
      (strongEtale_of_isQuasiIso _ D.presentation.isQuasiIso_directFromSaturation)
  change etale ((localizationFunctor.map (smallFibreProductSnd rf rg) ≫
    (recognitionSourceIso g).inv) ≫ localizationFunctor.map g)
  have h : localizationFunctor.map (smallFibreProductSnd rf rg) ≫
      ((recognitionSourceIso g).inv ≫ localizationFunctor.map g) =
    localizationFunctor.map (smallFibreProductSnd rf rg ≫ rg) ≫ (recognitionBaseIso X).inv := by
    rw [← recognitionMap_localized_inverse_square g, ← Category.assoc, ← Functor.map_comp]
  rw [Category.assoc, h]
  exact etale_comp (etale_map_of_strongEtale _ hsmall) (etale_of_isIso _)

private theorem exists_common_etale_product
    {A B X : LocalizedCategory.{u, v, v} (K := K)} {f : A ⟶ X} {g : B ⟶ X}
    (hf : etale f) (hg : etale g) :
    ∃ (P : LocalizedCategory.{u, v, v} (K := K)) (p : P ⟶ A) (q : P ⟶ B),
      IsPullback p q f g ∧ etale (q ≫ g) := by
  obtain ⟨A', hA⟩ := localizedObjectEquiv.surjective A
  change localizationFunctor.obj A' = A at hA
  subst A
  obtain ⟨B', hB⟩ := localizedObjectEquiv.surjective B
  change localizationFunctor.obj B' = B at hB
  subst B
  obtain ⟨X', hX⟩ := localizedObjectEquiv.surjective X
  change localizationFunctor.obj X' = X at hX
  subst X
  obtain ⟨φ, rfl⟩ := exists_localizedRightFraction f
  obtain ⟨ψ, rfl⟩ := exists_localizedRightFraction g
  have : IsIso (localizationFunctor.map φ.s) := (localizedQuasiIso φ.s φ.hs).isIso_hom
  have : IsIso (localizationFunctor.map ψ.s) := (localizedQuasiIso ψ.s ψ.hs).isIso_hom
  have hφ : strongEtale φ.f := by
    apply (etale_localizationFunctor_map_iff_strongEtale φ.f).mp
    rw [← localizationFunctor_map_s_comp_localizedRightFraction φ]
    exact etale_comp (etale_of_isIso _) hf
  have hψ : strongEtale ψ.f := by
    apply (etale_localizationFunctor_map_iff_strongEtale ψ.f).mp
    rw [← localizationFunctor_map_s_comp_localizedRightFraction ψ]
    exact etale_comp (etale_of_isIso _) hg
  let c := recognizedLocalizedPullback φ.f ψ.f AffinoidPushout.finiteBanachPushout hφ
  let hP := IsPullback.of_isLimit c.2
  refine ⟨c.1.pt, c.1.fst ≫ localizationFunctor.map φ.s, c.1.snd ≫ localizationFunctor.map ψ.s,
    ?_, ?_⟩
  · apply hP.of_iso (Iso.refl _) (localizedQuasiIso φ.s φ.hs)
      (localizedQuasiIso ψ.s ψ.hs) (Iso.refl _)
    · exact (Category.id_comp _).symm
    · exact (Category.id_comp _).symm
    · change localizationFunctor.map φ.f ≫ 𝟙 _ =
        localizationFunctor.map φ.s ≫ localizedRightFraction φ
      simpa only [Category.comp_id] using
        (localizationFunctor_map_s_comp_localizedRightFraction φ).symm
    · change localizationFunctor.map ψ.f ≫ 𝟙 _ =
        localizationFunctor.map ψ.s ≫ localizedRightFraction ψ
      simpa only [Category.comp_id] using
        (localizationFunctor_map_s_comp_localizedRightFraction ψ).symm
  · have he := recognizedLocalizedPullback_common_etale φ.f ψ.f hφ hψ
    rw [Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction]
    exact he

set_option linter.defProp false in
/-- The common structure map of any limiting product of two localized
étale arrows over the same base is itself étale. -/
def etale_common_of_isPullback
    {A B X P : LocalizedCategory.{u, v, v} (K := K)}
    {f : A ⟶ X} {g : B ⟶ X} {p : P ⟶ A} {q : P ⟶ B}
    (h : IsPullback p q f g) (hf : etale f) (hg : etale g) : etale (p ≫ f) := by
  obtain ⟨Q, a, b, hQ, he⟩ := exists_common_etale_product hf hg
  let e := h.isoIsPullback _ _ hQ
  have hs : e.hom ≫ b = q := h.isoIsPullback_hom_snd _ _ hQ
  have hcomp : e.hom ≫ (b ≫ g) = p ≫ f :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) hs).trans h.w.symm)
  exact hcomp ▸ etale_comp (etale_of_isIso e.hom) he

end Langlands.Analytic.SaturatedAtlasPresentation

import Langlands.Geometry.Analytic.ConditionalSmallEtaleProjection
import Langlands.Geometry.Analytic.RecognizedLocalizedPullbacks
import Langlands.Geometry.Analytic.LocalizedEtalePullbackReduction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteBanachPushout.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof

/-! # Exact localized etale pullbacks from the two general analytic criteria -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits PresentedAffinoidAlgebra AffinoidAtlasPresentation
open AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The existing small geometric second projection is canonically strong
etale, assuming exactly the general analytic criteria and comparison inputs. -/
theorem recognizedSmallProjection_strongEtale
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hupgrade : FinitePiecesEtaleAllPiecesStatement.{u, v, v} K)
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K)
    {A B X : SaturatedAtlasPresentation.{u, v, v} K}
    (f : A ⟶ X) (g : B ⟶ X) (hf : strongEtale f) :
    let _ := recognition_fibreProductSpace_small f g hpush hf
    strongEtale (smallFibreProductSnd (recognitionMap f) (recognitionMap g)) := by
  let _ := recognition_fibreProductSpace_small f g hpush hf
  let F : StrongHom A.presentation.saturatedPresentation X.presentation.saturatedPresentation :=
    (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f
  let G : StrongHom B.presentation.saturatedPresentation X.presentation.saturatedPresentation :=
    (compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map g
  let _ : Small.{v} (FibreProduct.chartSystem F.compatibleRecognitionMap G.compatibleRecognitionMap).Space :=
    recognition_fibreProductSpace_small f g hpush hf
  let q : ofSaturation (recognitionSmallProductPresentation F G) ⟶ ofSaturation G.recognitionSource :=
    (recognitionSmallSnd F G).saturationExtension
  have hq : strongEtale q :=
    (strongEtale_ofSaturation_iff q).mpr
      (recognitionSmallSnd_isEtaleAllPieces F G hlocal hupgrade hpush htensor hf)
  have he : (recognitionSource g).saturationIso.hom.IsQuasiIso :=
    (recognitionSource g).presentation.isQuasiIso_directFromSaturation
  exact strongEtale_comp hq (strongEtale_of_isQuasiIso _ he)

/-- All geometry, whole-map coefficients, size control and full localized
universality are constructed. The two remaining general analytic criteria
and finite algebra comparisons are explicit assumptions here. -/
theorem localizedEtalePullback_of_analyticCriteria
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hupgrade : FinitePiecesEtaleAllPiecesStatement.{u, v, v} K)
    (hpush : AffinoidPushout.FiniteBanachPushoutStatement K)
    (htensor : AffinoidPushout.FiniteTensorComparisonStatement K) :
    LocalizedEtalePullbackStatement.{u, v} K := by
  apply localizedEtalePullbackStatement_of_refinedStrong
  intro A B X f g hf
  let _ := recognition_fibreProductSpace_small f g hpush hf
  let c := recognizedLocalizedPullback f g hpush hf
  have hp : IsPullback c.1.fst c.1.snd (localizationFunctor.map f) (localizationFunctor.map g) :=
    IsPullback.of_isLimit c.2
  have he : etale c.1.snd :=
    etale_comp
      (etale_map_of_strongEtale (smallFibreProductSnd (recognitionMap f) (recognitionMap g))
        (recognizedSmallProjection_strongEtale hlocal hupgrade hpush htensor f g hf))
      (etale_of_isIso (recognitionSourceIso g).inv)
  exact exists_refinedStrongPullback_of_localized c.1.fst c.1.snd hp he

/-- The two algebraic comparison inputs are supplied by their published
unrestricted proofs. Exactly the two general analytic criteria remain. -/
theorem localizedEtalePullback_of_targetLocality_and_finitePieces
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hupgrade : FinitePiecesEtaleAllPiecesStatement.{u, v, v} K) :
    LocalizedEtalePullbackStatement.{u, v} K :=
  localizedEtalePullback_of_analyticCriteria hlocal hupgrade
    AffinoidPushout.finiteBanachPushout AffinoidPushout.finiteTensorComparison

/-- An actual limiting cone with the existing localized etale second leg,
under the explicit two general analytic criteria. This is conditional data,
not the unconditional proof required by Task 7349. -/
def conditionalLocalizedEtalePullback
    (hlocal : FiniteOverTargetLocalityStatement.{u, v, v} K)
    (hupgrade : FinitePiecesEtaleAllPiecesStatement.{u, v, v} K)
    {A B X : LocalizedCategory.{u, v, v} (K := K)}
    (f : A ⟶ X) (g : B ⟶ X) (hf : etale f) :
    Σ c : PullbackCone f g, IsLimit c × PLift (etale c.snd) :=
  Classical.choice (show Nonempty (Σ c : PullbackCone f g, IsLimit c × PLift (etale c.snd)) from by
    obtain ⟨P, p, q, hp, hq⟩ :=
      localizedEtalePullback_of_targetLocality_and_finitePieces hlocal hupgrade f g hf
    exact ⟨PullbackCone.mk p q hp.w, hp.isLimit, ⟨hq⟩⟩)

end Langlands.Analytic.SaturatedAtlasPresentation

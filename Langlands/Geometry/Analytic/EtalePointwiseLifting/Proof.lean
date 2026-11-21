import Langlands.Geometry.Analytic.EtalePointwiseLifting.FromLocalizedPullbacks
import Langlands.Geometry.Analytic.EtaleBaseChangeReduction
import Langlands.Geometry.Analytic.EtaleSectionsOpen
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof

/-! # Pointwise lifting in the analytic étale site -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

private theorem etale_rightCancellation_of_pullbacks
    (hpullback : LocalizedEtalePullbackStatement.{u, v} K) :
    MorphismProperty.HasOfPostcompProperty
      (etale (K := K) : MorphismProperty (LocalizedCategory.{u, v, v} (K := K)))
      (etale (K := K)) := by
  constructor
  intro A B X f g hg hfg
  obtain ⟨P, p, q, hP, hq⟩ := hpullback (f ≫ g) g hfg
  obtain ⟨_, _, _, hP', hp'⟩ := hpullback g (f ≫ g) hg
  have hp : etale p := etale_snd_of_isPullback hP' hP.flip hp'
  obtain ⟨s, hs, hsf⟩ := hP.exists_lift (𝟙 A) f (Category.id_comp _)
  have hse : etale s := by
    obtain ⟨U, hU, e, he⟩ := localizedEtaleSectionsOpen hp hs
    rw [← he]
    exact etale_comp (etale_of_isIso e.hom) (etaleOpenDomainStatement P U hU)
  exact hsf ▸ etale_comp hse hq

/-- Every compatible pair of ordinary points in the analytic étale site
lifts to an ordinary point of an actual commuting site square. -/
theorem etalePointwiseLifting : EtalePointwiseLiftingStatement.{u, v} K := by
  have hpullback : LocalizedEtalePullbackStatement.{u, v} K :=
    localizedEtalePullback_of_targetLocality_and_finitePieces
      (AffinoidAtlasPresentation.StrongHom.finiteOverTargetLocality_of_descent
        PresentedAffinoidAlgebra.finiteAffinoidAlgebraDescent)
      AffinoidAtlasPresentation.StrongHom.finitePiecesEtaleAllPieces
  exact etalePointwiseLifting_of_geometricInputs
    ⟨⟨inferInstance, etale_rightCancellation_of_pullbacks hpullback⟩,
      strongEtalePointwiseBaseChange_of_localizedEtalePullback hpullback⟩

end Langlands.Analytic.SaturatedAtlasPresentation

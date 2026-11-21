import Langlands.Geometry.Analytic.EtaleBaseChangeReduction
import Langlands.Geometry.Analytic.EtaleSectionsOpen
import Langlands.Geometry.Analytic.EtaleOpenDomains.Proof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof

/-! # Stability of localized analytic étale morphisms -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Localized analytic étale morphisms are closed under composition and
right cancellation by an étale morphism. -/
theorem localizedEtaleStability : LocalizedEtaleStabilityStatement.{u, v} K := by
  have hpullback : LocalizedEtalePullbackStatement.{u, v} K :=
    localizedEtalePullback_of_targetLocality_and_finitePieces
      (AffinoidAtlasPresentation.StrongHom.finiteOverTargetLocality_of_descent
        PresentedAffinoidAlgebra.finiteAffinoidAlgebraDescent)
      AffinoidAtlasPresentation.StrongHom.finitePiecesEtaleAllPieces
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro A B X f g hg hfg
  obtain ⟨P, p, q, hP, hq⟩ := hpullback (f ≫ g) g hfg
  obtain ⟨_, _, _, hFlipped, hp'⟩ := hpullback g (f ≫ g) hg
  have hp : etale p := etale_snd_of_isPullback hFlipped hP.flip hp'
  obtain ⟨s, hSection, hGraph⟩ := hP.exists_lift (𝟙 A) f (Category.id_comp _)
  have hs : etale s := by
    obtain ⟨U, hU, e, he⟩ := localizedEtaleSectionsOpen hp hSection
    rw [← he]
    exact etale_comp (etale_of_isIso e.hom) (etaleOpenDomainStatement P U hU)
  exact hGraph ▸ etale_comp hs hq

end Langlands.Analytic.SaturatedAtlasPresentation

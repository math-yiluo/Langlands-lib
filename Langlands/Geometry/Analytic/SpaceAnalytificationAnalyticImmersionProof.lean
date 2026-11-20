import Langlands.Geometry.Analytic.AnalyticClosedImmersionFromTests
import Langlands.Geometry.Analytic.SpaceAnalytificationAnalyticImmersionStatement
import Langlands.Geometry.Analytic.SpaceAnalytificationArtinianOpenReflection
import Langlands.Geometry.Analytic.SpaceAnalytificationDirectClosedReflection
import Langlands.Geometry.Analytic.SpaceAnalytificationDirectOpenPreservation

/-! # Open and closed immersions under algebraic-space analytification -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open SaturatedAtlasPresentation

/-- Analytification preserves and reflects open immersions, preserves closed immersions,
and reflects closed immersions for quasi-compact algebraic morphisms. -/
theorem spaceAnalytificationAnalyticImmersion :
    SpaceAnalytificationAnalyticImmersionStatement.{u} := by
  intro K _ _ _ X' X f hXs' hXt' hXs hXt Y' Y p' p hp' hp F hF
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact openImmersion_of_isOpenImmersion f F hp' hp hXs' hXt' hF
  · exact isOpenImmersion_of_openImmersion f hp' hp hXs' hXt' hXs hXt hF
  · intro hf
    refine closedImmersion_of_affinoidQuotientPullbacks F (fun R a => ?_)
    exact nonempty_affinoidQuotientPullback_of_isClosedImmersion (R := R) (a := a)
      hp' hp hXs' hXt' hXs hXt f hF hf
  · exact isClosedImmersion_of_closedImmersion f hp' hp hF hXs' hXt' hXs hXt

end Langlands.Analytic.SpaceAnalytification

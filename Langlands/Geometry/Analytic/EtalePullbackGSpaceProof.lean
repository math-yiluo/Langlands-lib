import Langlands.Geometry.Analytic.EtalePullbackGSpaceStatement
import Langlands.Geometry.Analytic.LocalizedPullbackCompactPreimages
import Langlands.Geometry.Analytic.LocalizedQuasiEtalePullbackAction

/-! # Fibre products along étale morphisms of `G`-spaces are `G`-spaces -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Specialize Hausdorffness and action continuity for localized pullbacks along
quasi-étale morphisms to the case of an étale morphism. -/
theorem etalePullbackGSpace : EtalePullbackGSpaceStatement.{u, v, z} K := by
  intro G _ _ A B Y P f g p q hf hP hA hB _ σ σA σB hσA hσB hp hq
  let : T2Space (localizedSpaceFunctor.obj A) := hA
  let : T2Space (localizedSpaceFunctor.obj B) := hB
  have hfq := etale_le_quasiEtale f hf
  exact ⟨(hasCompactPairPreimages_of_quasiEtale hP hfq).1,
    isContinuousAction_of_isPullback_of_quasiEtale hP hfq hσA hσB hp hq⟩

end Langlands.Analytic.SaturatedAtlasPresentation

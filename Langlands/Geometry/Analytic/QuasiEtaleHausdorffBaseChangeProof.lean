import Langlands.Geometry.Analytic.QuasiEtaleHausdorffStabilityStatement
import Langlands.Geometry.Analytic.QuasiEtaleBaseChangeReduction

/-! # Quasi-étale base change for Hausdorff sources -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Base change of a quasi-étale arrow with Hausdorff source is quasi-étale, in every
pullback square: this is `quasiEtale_of_isPullback_of_t2Space`. -/
theorem quasiEtaleHausdorffBaseChange : QuasiEtaleHausdorffBaseChangeStatement.{u, v} K :=
  fun sq hY hg => by
    have := hY
    exact quasiEtale_of_isPullback_of_t2Space sq hg

end Langlands.Analytic.SaturatedAtlasPresentation

import Langlands.Geometry.Building.SimplyConnectedReflectionTranslationStatement
import Langlands.Geometry.Building.SimplyConnectedReflectionTranslationReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.SimplyConnected.RankOneCentralizerGenerationProof

/-! # Simply connected realization of actual centralizer translations: proof -/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **Reflection translations of simply connected groups.** For valuation building data of a
simply connected group over a nonarchimedean local field, the translation lattice of the
reflection normalizer equals the translation lattice of the centralizer. -/
theorem simplyConnectedReflectionTranslation :
    SimplyConnectedReflectionTranslationStatement.{u} :=
  simplyConnectedReflectionTranslation_of_rankOneGeneration rootRankOneFactorization
    simplyConnectedRankOneCentralizerGeneration

end Langlands.Geometry.Building

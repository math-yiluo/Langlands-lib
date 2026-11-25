import Langlands.Geometry.Building.SimplyConnectedFacetFixingStatement
import Langlands.Geometry.Building.SimplyConnectedFacetFixingReduction
import Langlands.GroupScheme.SimplyConnected.RankOneCentralizerGenerationProof

/-! # Simply connected normalizer facet stabilizers: proof -/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **Facet fixing for simply connected groups** (Kaletha–Prasad 9.3.26, restricted to the
normalizer). For valuation building data of a simply connected group over a nonarchimedean
local field, every point of the normalizer of the maximal split torus that preserves an
apartment facet as a set fixes it pointwise. -/
theorem simplyConnectedFacetFixing : SimplyConnectedFacetFixingStatement.{u} :=
  simplyConnectedFacetFixing_of_rankOneCentralizerGeneration
    simplyConnectedRankOneCentralizerGeneration

end Langlands.Geometry.Building

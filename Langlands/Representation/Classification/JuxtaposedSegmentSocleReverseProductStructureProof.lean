import Langlands.Representation.Classification.JuxtaposedConditionalAssembly
import Langlands.Representation.Classification.JuxtaposedNonadjacentPairIrreducible
import Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof
import Langlands.Representation.Classification.TwoSegmentSocleShuffleJacquetProof

/-!
# Zelevinsky 1980, Proposition 4.6, step (1): the juxtaposed case

The product `⟨Δ⟩ × ⟨Δ'⟩` of two segment socles with `Δ'` preceding and juxtaposed
with `Δ` has length two, its unique irreducible subrepresentation is not equivalent
to `⟨Δ' ∪ Δ⟩`, and its quotient by that subrepresentation is. This file assembles
the conditional theorem of `JuxtaposedConditionalAssembly` with the published
shuffle-Jacquet count (`twoSegmentSocleShuffleJacquet`) and Zelevinsky 1.11(a)
(`twoSupercuspidalNonadjacentProductIrreducible`).
-/

namespace Langlands.Classification

universe uF uV

/-- Zelevinsky 1980, Proposition 4.6, step (1), for juxtaposed segments. -/
theorem juxtaposedSegmentSocleReverseProductStructure
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T :=
  JuxtaposedShuffle.juxtaposedSegmentSocleReverseProductStructure_of_irreducible T
    (twoSegmentSocleShuffleJacquet F T)
    fun hr A a b hab => JuxtaposedShuffle.uniform_two_isIrreducible_of_nonadjacent T
      (twoSupercuspidalNonadjacentProductIrreducible F T) hr A a b hab

end Langlands.Classification

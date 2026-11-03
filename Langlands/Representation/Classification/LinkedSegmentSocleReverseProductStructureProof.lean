import Langlands.Representation.Classification.LinkedSegmentSocleReverseProductConditional
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof
import Langlands.Representation.Classification.UnlinkedSegmentSocleProductIrreducibleProof
import Langlands.Representation.Classification.JuxtaposedSegmentSocleReverseProductStructureProof
import Langlands.Representation.Classification.LinkedSegmentSocleReverseProductQuotientHomProof
import Langlands.Representation.Classification.NonjuxtaposedSegmentSocleDerivativeStrictMonoProof
import Langlands.Representation.Classification.SegmentSocleProductHighestDerivativeProof

/-! Zelevinsky 1980, Proposition 4.6, for a linked pair of segment socles in
precedence order: the conditional proof applied to the seven published inputs. -/

namespace Langlands.Classification

universe uF uV

/-- Zelevinsky 1980, Proposition 4.6: for segment socles `⟨Δ⟩, ⟨Δ'⟩` with `Δ'`
preceding `Δ`, the product `⟨Δ⟩ × ⟨Δ'⟩` has length two. Its top factor is the
irreducible product `⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩` (the intersection omitted when the
segments are juxtaposed), and its bottom factor, not isomorphic to that product,
is its unique irreducible subrepresentation. -/
theorem linkedSegmentSocleReverseProductStructure {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LinkedSegmentSocleReverseProductStructure.{uF, uV} F T :=
  linkedSegmentSocleReverseProductStructure_of
    (HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T)
    (segmentZelevinskyConstituentExistence F T)
    (unlinkedSegmentSocleProductIrreducible F T)
    (juxtaposedSegmentSocleReverseProductStructure F T)
    (linkedSegmentSocleReverseProductQuotientHom F T)
    (nonjuxtaposedSegmentSocleDerivativeStrictMono F T)
    (segmentSocleProductHighestDerivative F T)

end Langlands.Classification

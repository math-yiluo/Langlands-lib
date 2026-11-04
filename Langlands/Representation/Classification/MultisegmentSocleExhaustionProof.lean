import Langlands.Representation.Classification.AdjacentUnlinkedSegmentSocleSwapProof
import Langlands.Representation.Classification.LinkedSegmentSocleEmbeddingReductionProof
import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.OrderedMultisegmentSocleExistenceProof
import Langlands.Representation.Classification.SegmentSocleEmbeddingExistence
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof

/-!
# Independent Zelevinsky multisegment socle exhaustion

Starting from an actual cuspidal-product embedding, the two proved local rules
and integral twist freeness give an inversion-minimal ordered segment-socle
product. Its independently proved strong socle property transfers to the given
irreducible embedding. This is Zelevinsky 1980, Theorem 6.1(c), §§6.5 and 6.7.
-/

noncomputable section

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every irreducible smooth representation, including at rank zero, is the
strong socle of an actual ordered product of segment socles. -/
theorem multisegmentSocleExhaustion : MultisegmentSocleExhaustion.{uF, uV} F T := by
  let := T.topology
  intro n π hπ
  have hlocal :
      PadicField.TopologicalData.HasIndexedSocleEmbeddingReductions.{uF, max uF uV} π := by
    constructor
    · intro d j h hu hd
      obtain ⟨e⟩ := adjacentUnlinkedSegmentSocleSwap.{uF, uV} F T n d hd.1 j h hu
      exact ⟨hd.1.permute _, hd.2.of_equiv (SmoothRep.equivOfIso e)⟩
    · intro d j h hp hd
      rcases linkedSegmentSocleEmbeddingReduction.{uF, uV} F T n d π hd.1 hd.2 j h hp with
          hswap | ⟨U, I, e, hU, hI, he, heSocles, heEmbed⟩
      · exact Or.inl ⟨hd.1.permute _, hswap⟩
      · exact Or.inr ⟨U, I, e, ⟨hU, hI⟩, he, heSocles, heEmbed⟩
  obtain ⟨d, hdOrdered, hdEmbed⟩ := hlocal.exists_ordered
    (cuspidalIntegralTwistFreeness.{uF, max uF uV} F T)
    (T.exists_segmentSocleEmbedding π hπ)
  exact ⟨d.multisegment, d.multisegment_degree,
    d, rfl, hdEmbed.isZelevinskySocle_of_exists
      (orderedMultisegmentSocleExistence.{uF, uV} F T n d hdOrdered hdEmbed.1)⟩

end Langlands.Classification

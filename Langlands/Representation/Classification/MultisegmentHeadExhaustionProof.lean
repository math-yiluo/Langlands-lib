import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.OrderedMultisegmentHeadExistenceProof
import Langlands.Representation.Classification.OrderedMultisegmentQuotientExhaustionProof

/-!
# Multisegment special-head exhaustion

Retain the quotient map to the given irreducible input and obtain its kernel
uniqueness from a strong head of the same ordered segment product.
-/

namespace Langlands.Classification

open PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every irreducible smooth input is the strong head of an actual ordered
special-segment product, with multisegment degree equal to its rank. -/
theorem multisegmentHeadExhaustion :
    MultisegmentHeadExhaustion.{uF, uV} F T := by
  let := T.topology
  intro n π hπ
  obtain ⟨d, ho, hh, hπq, q, hq⟩ :=
    orderedMultisegmentQuotientExhaustion.{uF, uV} F T n π hπ
  obtain ⟨π₀, _, _, _, q₀, _, hker⟩ :=
    orderedMultisegmentHeadExistence.{uF, uV} F T n d ho hh
  refine ⟨d.multisegment, ?_, d, rfl, ho, hh, hπq, q, hq, ?_⟩
  · dsimp only [SegmentProductDatum.multisegment, Multisegment.degree]
    rw [Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
    exact d.degree_sum
  · intro W' _ _ π' hπ' q' hq'
    exact (hker W' π' hπ' q' hq').trans
      (hker _ π.representation hπq q hq).symm

end Langlands.Classification

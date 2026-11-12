import Langlands.Representation.Classification.ZeroRankMultisegmentQuotientProof
import Langlands.Representation.Classification.TemperedLanglandsQuotientCoverageProof
import Langlands.Representation.Classification.TemperedSpecialSegmentRefinementProof

/-!
# Ordered special-segment quotient coverage

Combine rank-zero coverage with positive-rank tempered quotient coverage and
the refinement of tempered standard modules into ordered special segments.
-/

namespace Langlands.Classification

universe uF uV

/-- Every irreducible smooth representation is an actual quotient of a
nonprecedence-ordered product of strong special segment heads. -/
theorem orderedMultisegmentQuotientExhaustion
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    OrderedMultisegmentQuotientExhaustion.{uF, uV} F T := by
  let := T.topology
  intro n
  cases n with
  | zero => exact zeroRankMultisegmentQuotientExhaustion.{uF, uV} F T
  | succ n =>
    intro π hπ
    obtain ⟨t, ht⟩ :=
      temperedLanglandsQuotientCoverage.{uF, uV} F T (n + 1) (Nat.succ_pos n) π hπ
    obtain ⟨d, ho, hh, ⟨e⟩⟩ :=
      temperedSpecialSegmentRefinement.{uF, uV} F T (n + 1) (Nat.succ_pos n) t
    exact ⟨d, ho, hh,
      IsIrreducibleQuotient.of_equiv (SmoothRep.equivOfIso e).symm ht⟩

end Langlands.Classification

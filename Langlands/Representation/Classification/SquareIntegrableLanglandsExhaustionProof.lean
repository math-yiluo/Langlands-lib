import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.TemperedLanglandsQuotientCoverageProof
import Langlands.Representation.Classification.RegularLanglandsHeadExistenceProof
import Langlands.Representation.Classification.TemperedSpecialSegmentRefinementProof
import Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionProof

/-!
# Exhaustion by square-integrable Langlands heads

Promote the supplied tempered quotient map to a strong head using regular
kernel uniqueness, then refine and reorder its actual inducing product.
-/

namespace Langlands.Classification

open CategoryTheory

universe uF uV

/-- Every positive-rank irreducible smooth representation is the strong head
of genuine square-integrable Langlands data. -/
theorem squareIntegrableLanglandsExhaustion
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SquareIntegrableLanglandsExhaustion.{uF, uV} F T := by
  let := T.topology
  intro n hn π hπ
  obtain ⟨t, _, q, hq⟩ := temperedLanglandsQuotientCoverage.{uF, uV} F T n hn π hπ
  obtain ⟨_, _, q₀, hq₀, hker⟩ :=
    glRegularLanglandsHeadExistence.{uF, uV} p F T n hn t
  have hhead : t.IsLanglandsHead π := by
    refine ⟨hπ, q, hq, ?_⟩
    intro W _ _ τ hτ q' hq'
    exact (hker W τ hτ q' hq').trans (hker _ π.representation hπ q hq).symm
  obtain ⟨d, ho, hh, ⟨a⟩⟩ := temperedSpecialSegmentRefinement.{uF, uV} F T n hn t
  obtain ⟨e, ⟨b⟩, _⟩ :=
    orderedSegmentSquareIntegrableConversion.{uF, uV} F T n hn d ho hh
  exact ⟨e, IsIrreducibleHead.of_equiv
    (SmoothRep.equivOfIso (a.symm ≪≫ b)) hhead⟩

end Langlands.Classification

import Langlands.Representation.Classification.SegmentHeadJacquetReduction
import Langlands.Representation.Classification.SegmentFullJacquetProof
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof

/-!
# Two-block Jacquet modules of special segment heads

Zelevinsky 1980, Proposition 9.5, from the conditional reduction
`SegmentHeadJacquetReduction.segmentHeadJacquetFormula_of` and the published proofs of
Ze80 9.1(*), BZ77 2.13(b), Ze80 9.1 and BZ77 2.8.
-/

namespace Langlands.Classification

open CuspidalSupport

universe uF uV

/-- Zelevinsky 1980, Proposition 9.5: for a special segment head `π` of `Δ`, the
normalized Jacquet module of `π` along `(n - l, l)` vanishes unless `r ∣ l`, and along
the split `((m - q) r, q r)` it is isomorphic to the external tensor product of the
terminal and initial heads. -/
theorem segmentHeadJacquetFormula
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentHeadJacquetFormula.{uF, uV} F T :=
  SegmentHeadJacquetReduction.segmentHeadJacquetFormula_of T
    (segmentFullJacquetFormula.{uF, uV} F T).2
    (fun n => nonassociatedJacquetSubquotients F T n)
    (segmentSpecialConstituentExistence F T)
    (fun n => cuspidalInductionLength F T n)

end Langlands.Classification

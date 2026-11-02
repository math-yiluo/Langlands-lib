import Langlands.Representation.Classification.SegmentSocleJacquetReduction
import Langlands.Representation.Classification.SegmentFullJacquetProof
import Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof

/-! Zelevinsky 1980, Proposition 3.4: the two-block Jacquet modules of segment socles. -/

namespace Langlands.Classification

universe uF uV

/-- **Zelevinsky 1980, Proposition 3.4.** The normalized Jacquet module of the segment
socle `⟨Δ⟩` along `(l, n - l)` vanishes unless `r ∣ l`, and along `(q r, (m - q) r)` it
is isomorphic to `⟨Δ.initial q⟩ ⊗ ⟨Δ.terminal q⟩` for actual socles of the two shorter
segments. -/
theorem segmentSocleJacquetFormula
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentSocleJacquetFormula.{uF, uV} F T :=
  SegmentSocleJacquetReduction.segmentSocleJacquetFormula_of T
    (segmentFullJacquetFormula F T).1
    (fun n => CuspidalSupport.nonassociatedJacquetSubquotients F T n)
    (segmentZelevinskyConstituentExistence F T)
    (fun n => CuspidalSupport.cuspidalInductionLength F T n)

end Langlands.Classification

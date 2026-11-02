import Langlands.Representation.Classification.RepeatedCuspidalTripleJacquetTransferStatement
import Langlands.Representation.CuspidalSupport.TripleTransferReduction
import Langlands.Representation.CuspidalSupport.LocalTripleSeeds

/-! Both repeated-factor cuspidal triple Jacquet transfers. -/

namespace Langlands.Classification

universe uF uV

/-- Both exact ambient repeated-factor transfers, with the supplied field,
topological data and unrestricted outside factors. -/
theorem repeatedCuspidalTripleJacquetTransfer
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T :=
  CuspidalSupport.repeatedCuspidalTripleJacquetTransfer_of_uniform F T
    (CuspidalSupport.uniformRepeatedCuspidalTripleJacquetTransfer F T)

end Langlands.Classification

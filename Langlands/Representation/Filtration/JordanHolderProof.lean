import Langlands.Representation.Filtration.JordanHolderComparisonProof
import Langlands.Representation.Filtration.JordanHolderTransportProof

/-! Comparison, transport and transitivity for actual Jordan–Hölder series. -/

namespace Langlands

universe uK uG uA uB uC

/-- Actual supplied-series comparison, transport, and multiplicity-sensitive transitivity. -/
theorem jordanHolderSeries : JordanHolderSeriesStatement.{uK, uG, uA, uB, uC} :=
  ⟨jordanHolderSeriesComparison.{uK, uG, uA},
    jordanHolderSeriesTransport.{uK, uG, uA, uB},
    haveSameJordanHolderFactors_trans.{uK, uG, uA, uB, uC}⟩

end Langlands

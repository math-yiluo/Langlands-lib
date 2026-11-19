import Langlands.GroupScheme.Reductive.OuterIsomorphismFromPinnedCharts
import Langlands.GroupScheme.Reductive.PinnedOuterIsomorphismChartProof

/-! # Existence of actual outer-isomorphism quotients over a DVR -/

universe u

namespace Langlands.GroupScheme

/-- The supplied full-centre quotient and Isom representative admit an actual outer quotient. -/
theorem genericOuterIsomorphismSchemeExistence :
    GenericOuterIsomorphismSchemeExistenceStatement.{u} :=
  genericOuterIsomorphismSchemeExistence_of_pinnedCharts pinnedOuterIsomorphismChart

end Langlands.GroupScheme

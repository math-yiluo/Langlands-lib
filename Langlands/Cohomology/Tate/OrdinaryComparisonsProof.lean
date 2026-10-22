import Langlands.Cohomology.Tate.OrdinaryComparisonStatement
import Langlands.Cohomology.Tate.PositiveCorestriction
import Langlands.Cohomology.Tate.NegativeTransferComparison

universe u

namespace Langlands.Tate

/-- The constructed Tate maps agree with the independently defined ordinary maps. -/
theorem ordinaryComparisons : OrdinaryComparisons.{u} := by
  intro R G _ _ _ H _ _ A n _
  exact ⟨restriction_groupCohomology H A n, corestriction_groupCohomology H A n,
    corestriction_groupHomology H A n, restriction_groupHomology H A n⟩

end Langlands.Tate

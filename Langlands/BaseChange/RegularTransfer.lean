import Langlands.BaseChange.RegularOrbitalProfileExistence
import Langlands.BaseChange.RegularOrbitalProfilesFromCharts
import Langlands.BaseChange.RegularOrbitParameters
import Langlands.BaseChange.RegularTransferCharts
import Langlands.BaseChange.RegularTransferReduction

/-! Regular-support transfer from the normalized profiles on the two general linear groups. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Set _root_.Topology
open Langlands.JacquetLanglands Langlands.TraceFormula
open Langlands.Topology (HasCompactOpenNeighborhoodBasis hasCompactOpenNeighborhoodBasis_of_mathlib)
open SigmaLiftCharacterIdentity (coefficients coefficients_conj continuous_coefficients)

universe u v

/-- Regularly supported test functions transfer in both directions for cyclic base change. -/
theorem regularTransfer : RegularTransferStatement.{u, v} :=
  regularTransferReduction regularOrbitalProfileExistence
    (by
      intro F _ E _ _ n γ hγ a b ha hb
      exact commute_of_regular_baseChange hγ ha hb)

end Langlands.BaseChange

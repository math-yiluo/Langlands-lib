import Langlands.Global.Arithmetic.IdeleClassPowerQuotientProfiniteStatement
import Langlands.Global.Arithmetic.SUnitIdelePowerQuotient
import Langlands.Global.Arithmetic.IdelePowerQuotientCover
import Langlands.Topology.OpenSubgroupPowerQuotient

/-! # Profinite positive-power quotients of actual idele classes -/

universe u

namespace Langlands.Global

open Arithmetic.IdeleSUnits Arithmetic.IdelePowerQuotientCover
open Arithmetic.SUnitIdeleTopology Arithmetic.SUnitIdelePowerQuotient

/-- Actual idele classes modulo any positive natural power range form a
Hausdorff compact totally disconnected group, with their quotient topology. -/
theorem ideleClassPowerQuotientProfinite_proof :
    IdeleClassPowerQuotientProfiniteStatement.{u} := by
  intro K _ _ m hm
  have h := sUnitIdeles_powerQuotient_profinite K (places K) m (Nat.ne_of_gt hm)
  let := h.1
  let := h.2.1
  let := h.2.2
  exact Langlands.openSubgroupPowerQuotient_profinite_of_fg
    (principalIdeles K) (sUnitIdeles K (places K)) m
    (isOpen_sUnitIdeles K (places K)) (principal_sup K)
    (principal_intersection_fg K (places K)) hm

end Langlands.Global

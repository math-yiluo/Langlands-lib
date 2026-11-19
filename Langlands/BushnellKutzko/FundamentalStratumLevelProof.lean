import Langlands.BushnellKutzko.FundamentalStratumLevelCore
import Langlands.BushnellKutzko.FundamentalStratumLevelStatement

/-! # Proof of L1: a fundamental stratum computes the normalized level

Bushnell (1987), Remark (2.9), printed p. 195, and (3.3) and Theorem 2′, printed
pp. 196–197. See also Bushnell–Kutzko (1993), Introduction, printed p. 8, and §2.3,
printed p. 57.

The published statement `FundamentalStratumLevelStatement` follows from its body, which is
proved as `fundamentalStratumLevel_of_containsStratum` in
`Langlands.BushnellKutzko.FundamentalStratumLevelCore`.
-/

namespace Langlands.BushnellKutzko

universe uK uV

/-- A contained fundamental stratum computes the normalized level of the representation. -/
theorem fundamentalStratumLevel : FundamentalStratumLevelStatement.{uK, uV} :=
  fun _ _ K n hn ψ hψ a 𝓛 m b hm hb hfund hcont =>
    fundamentalStratumLevel_of_containsStratum K n hn ψ hψ a 𝓛 m b hm hb hfund hcont

end Langlands.BushnellKutzko

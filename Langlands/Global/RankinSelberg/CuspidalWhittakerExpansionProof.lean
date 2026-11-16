import Langlands.Global.RankinSelberg.ProjectionExpansionReduction
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionRealization

/-! # Proof of the Whittaker expansion of the cusp forms of cuspidal realizations

Proof of `Langlands.Global.RankinSelbergGlobal.CuspidalWhittakerExpansionStatement`
(Cogdell 2004, Theorem 1.1, for the vectors of an actual cuspidal operator realization). The
work is done in the modules `Langlands.Global.RankinSelberg.WhittakerExpansionCore.*`; the final
step is `Unfolding.cuspidalWhittakerExpansion` (module `ExpansionRealization`). -/

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- **The Whittaker expansion of the cusp forms of actual cuspidal realizations.** -/
theorem cuspidalWhittakerExpansionStatement_proof : CuspidalWhittakerExpansionStatement.{u} :=
  fun F _ _ _ _ T => Unfolding.cuspidalWhittakerExpansion F T

end Langlands.Global.RankinSelbergGlobal

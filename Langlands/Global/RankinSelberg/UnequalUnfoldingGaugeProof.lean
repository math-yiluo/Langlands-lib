import Langlands.Global.RankinSelberg.UnequalGaugeReduction
import Langlands.Global.RankinSelberg.UnequalPadGaugeProof
import Langlands.Global.RankinSelberg.UnequalRectGaugeProof

/-! # The gauge integrability premises of the unequal-rank unfolding

Proof of `UnequalUnfoldingGaugeStatement` (premises G and G' of
`UnequalUnfoldingReductionStatement` for every actual positive unequal-rank cuspidal pair),
from the published reduction `unequalGaugeReduction` and the published Whittaker gauge bounds
`unequalPadGauge` and `unequalRectGauge`.
-/

universe u
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Premises G and G' of the unequal-rank unfolding hold for every actual positive
unequal-rank cuspidal pair over every number field `F : Type u` whose additive adelic
quotient is compact. -/
theorem unequalUnfoldingGauge : UnequalUnfoldingGaugeStatement.{u} :=
  unequalGaugeReduction unequalPadGauge unequalRectGauge

end Langlands.Global.RankinSelbergGlobal

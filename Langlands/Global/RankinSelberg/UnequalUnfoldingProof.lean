import Langlands.Global.RankinSelberg.UnequalUnfoldingAssembly
import Langlands.Global.RankinSelberg.UnequalPadGaugeProof
import Langlands.Global.RankinSelberg.WhittakerSimpleRootMajorization
import Langlands.Global.RankinSelberg.UnequalRectGaugeOfSimpleRootGauge
import Langlands.Global.RankinSelberg.RectangularGaugeMellinProof

/-! # Proof of the ordinary and dual unfolding for unequal-rank cuspidal pairs

This module proves `UnequalUnfoldingStatement` (Cogdell 2004, §2.2). It combines published
results: the conditional assembly `unequalUnfolding_of_whittakerGauges`, the padded gauge
bound `unequalPadGauge`, and the rectangular gauge bound. The rectangular bound is obtained
from `unequalRectGauge_of_simpleRootGauge` applied to `whittakerSimpleRootMajorization` and
`adelicSimpleRootGaugeRectangularMellin`.
-/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The ordinary and dual unfolding for every actual positive unequal-rank cuspidal pair over
every number field `F : Type u` whose additive adelic quotient is compact. -/
theorem unequalUnfoldingStatement_proof : UnequalUnfoldingStatement.{u} :=
  unequalUnfolding_of_whittakerGauges unequalPadGauge
    (unequalRectGauge_of_simpleRootGauge whittakerSimpleRootMajorization
      adelicSimpleRootGaugeRectangularMellin)

end Langlands.Global.RankinSelbergGlobal

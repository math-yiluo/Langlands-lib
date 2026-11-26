import Langlands.Global.RankinSelberg.ComplexGapTorusBound
import Langlands.Global.RankinSelberg.RealTwoBlockIwasawa
import Langlands.Global.RankinSelberg.RealConvergenceAnalysis

/-! # Exponential domination in the two-block real torus -/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapTorusBound

export ComplexGapTorusBound (blockLog_last exponent_le exponent_le_first torusEnvelope)

/-- For a sufficiently large first-block exponent, the envelope with sufficiently large
simple-root and Schwartz decay rates is integrable for product torus Lebesgue measure. -/
def RealGapTorusBoundStatement : Prop :=
  ComplexGapTorusBound.ComplexGapTorusBoundStatement

theorem realGapTorusBound : RealGapTorusBoundStatement :=
  ComplexGapTorusBound.complexGapTorusBound

end Langlands.Global.RankinSelbergGlobal.RealGapTorusBound

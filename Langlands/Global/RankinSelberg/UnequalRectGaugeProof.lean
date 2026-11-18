import Langlands.Global.RankinSelberg.UnequalRectGaugeOfSimpleRootGauge
import Langlands.Global.RankinSelberg.WhittakerSimpleRootMajorization
import Langlands.Global.RankinSelberg.RectangularGaugeMellinProof

/-! # The unequal-rank rectangular Whittaker gauge bound -/

universe u
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The rectangular gauge bound for every actual unequal-rank cuspidal
realization, with a threshold uniform in the character and vector. -/
theorem unequalRectGauge : UnequalRectGaugeStatement.{u} :=
  unequalRectGauge_of_simpleRootGauge
    whittakerSimpleRootMajorization adelicSimpleRootGaugeRectangularMellin

end Langlands.Global.RankinSelbergGlobal

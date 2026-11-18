import Langlands.Global.RankinSelberg.EqualGaugeAnalyticReduction
import Langlands.Global.RankinSelberg.WhittakerSchwartzGauge

/-! # Gauge integrability for the equal-rank unfolding -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Both equal-rank gauge premises, uniformly in the standard character,
vectors and Schwartz–Bruhat function. -/
theorem equalUnfoldingGauge : EqualUnfoldingGaugeStatement.{u} :=
  equalGaugeAnalyticReduction.{u} whittakerSchwartzGauge.{u}

end Langlands.Global.RankinSelbergGlobal

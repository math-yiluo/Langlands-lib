import Langlands.Global.RankinSelberg.EqualGaugeSpecialization
import Langlands.Global.RankinSelberg.EqualGaugeDualSpecialization

/-! # The equal-rank gauge premises from one analytic estimate

The primal and dual specializations of the common Whittaker–Schwartz estimate
together give the unchanged equal-rank gauge proposition. -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The common analytic estimate implies both equal-rank gauge premises. -/
def EqualGaugeAnalyticReductionStatement : Prop :=
  WhittakerSchwartzGaugeStatement.{u} → EqualUnfoldingGaugeStatement.{u}

/-- Combine the primal and dual specializations without changing the target. -/
theorem equalGaugeAnalyticReduction : EqualGaugeAnalyticReductionStatement.{u} := by
  intro h
  exact ⟨equalGaugeReduction (equalGaugeSpecialization h), equalGaugeDualSpecialization h⟩

end Langlands.Global.RankinSelbergGlobal

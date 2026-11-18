import Langlands.Global.RankinSelberg.EqualEulerGaugeReduction
import Langlands.Global.RankinSelberg.WhittakerSchwartzGauge

/-! # Proof of the equal-rank partial Euler factorization

`EqualEulerFactorizationStatement` (Cogdell 2004, §2.3, p.210, with Theorem 3.3, p.215)
follows from the published reduction `equalEulerFactorization_of_whittakerSchwartzGauge`
applied to the published estimate `whittakerSchwartzGauge`. See the paired Markdown.
-/

noncomputable section
universe u uQ
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- **Cogdell 2004, §2.3, p.210, with Theorem 3.3, p.215**: the equal-rank global Whittaker
integral converges absolutely in a right half-plane and factors as the partial integral over
`S ∪ ∞` times the Euler product of the unramified pair factors outside `S`. -/
theorem equalEulerFactorization : EqualEulerFactorizationStatement.{u, uQ} :=
  equalEulerFactorization_of_whittakerSchwartzGauge whittakerSchwartzGauge

end Langlands.Global.RankinSelbergGlobal

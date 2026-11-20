import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.AdelicIntertwiningConvergenceReduction

/-! # Absolute convergence of adelic intertwining integrals -/

universe u

namespace Langlands.Global

/-- The adelic intertwining integrand admits an integrable majorant uniform on compact sets
of adelic arguments and sufficiently regular parameters (Mœglin–Waldspurger II.1.6 (i)). -/
theorem intertwiningAbsoluteConvergence : IntertwiningAbsoluteConvergenceStatement.{u} :=
  intertwiningAbsoluteConvergence_of_eisenstein eisensteinAbsoluteConvergence

end Langlands.Global

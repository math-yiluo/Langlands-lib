import Langlands.Global.AdelicFunctoriality.MixedWeakApproximationStatement
import Langlands.Global.AdelicFunctoriality.MixedWeakApproximation

/-! # Proof of mixed principal-idele approximation -/

namespace Langlands.Global.AdelicFunctoriality

universe u

/-- The named mixed principal-idele approximation proposition follows directly
from Worker 226's published multiplicative weak approximation theorem. -/
theorem mixedPrincipalIdeleApproximation : MixedPrincipalIdeleApproximation.{u} := by
  intro K _ _ S a U hU V hV
  exact exists_principal_inv_mul_mem S a U hU V hV

end Langlands.Global.AdelicFunctoriality

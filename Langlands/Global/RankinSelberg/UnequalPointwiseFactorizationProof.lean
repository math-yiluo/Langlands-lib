import Langlands.Global.RankinSelberg.ComplexUnequalOrdinaryPlaceTestsProof
import Langlands.Global.RankinSelberg.RealUnequalOrdinaryPlaceTestsProof
import Langlands.Global.RankinSelberg.UnequalPointwiseFactorizationFromGlobalReflection

/-! # Pointwise factorization of unequal-rank Rankin–Selberg integrands -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

/-- The ordinary and dual unequal-rank kernels factor on the integral unipotent classes
for one pair of global test vectors. -/
theorem unequalPointwiseFactorization : UnequalPointwiseFactorizationStatement.{u,uQ} := by
  apply unequalPointwiseFactorizationFromGlobalReflection realUnequalOrdinaryPlaceTests
  intro F _ _ _ ψ hψ r t h _
  exact complexUnequalOrdinaryPlaceTests F ψ hψ r t h

end Langlands.Global.RankinSelbergGlobal

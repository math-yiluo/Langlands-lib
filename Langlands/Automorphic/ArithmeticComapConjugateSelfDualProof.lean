import Langlands.Automorphic.CuspidalArithmeticTransportStatement
import Langlands.Automorphic.ConjugateContragredientArithmeticTransport

/-!
# Arithmetic pullback preserves conjugate self-duality

For CM fields `K`, `L` and a ring isomorphism `e : K ≃+* L`, the arithmetic pullback of
a conjugate self-dual irreducible cuspidal class over `L` is conjugate self-dual over
`K`. The proof is
`CuspidalOperatorRealization.IsoClass.IsConjugateSelfDual.arithmeticComap`, which pulls a
full conjugate-contragredient pairing back through `arithmeticComapEquiv`. This proves
`ArithmeticComapConjugateSelfDualStatement` at independent field universes.
-/

noncomputable section

universe uK uL

set_option autoImplicit false

namespace Langlands.Automorphic

/-- Arithmetic pullback along a ring isomorphism of CM fields preserves conjugate
self-duality of irreducible cuspidal classes. -/
theorem arithmeticComapConjugateSelfDual :
    ArithmeticComapConjugateSelfDualStatement.{uK, uL} := by
  intro K L _ _ _ _ _ _ _ _ e r c hc
  exact CuspidalOperatorRealization.IsoClass.IsConjugateSelfDual.arithmeticComap e hc

end Langlands.Automorphic

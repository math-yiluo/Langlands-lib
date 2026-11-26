import Langlands.Global.Arithmetic.HarrisWeakInductionConjugateSelfDualProof

/-!
# Conjugate self-duality of a weak induction, totally complex rigidity premise

The proof of `WeakInductionConjugateInverseSelfDualTCStatement`: the core result
`isConjugateSelfDual_of_isWeakAutomorphicInductionOf_of_isConjugateInverse` needs Euler
constituent recovery only at the base field `E`, which is CM and hence totally complex, so the
totally complex form `CuspidalSpectralRigidityTCStatement` supplies it.
-/

noncomputable section

universe uV uE uE'

set_option autoImplicit false

namespace Langlands.Global.Harris

/-- `WeakInductionConjugateInverseSelfDualTCStatement`: given the totally complex form of
spectral rigidity, a weak automorphic induction over a CM field `E` of a conjugate-inverse
Hecke character of a CM extension `E'` is conjugate self-dual. The Euler constituent recovery
component of the premise is applied at `E`, which is totally complex because it is CM. -/
theorem weakInductionConjugateInverseSelfDualTC :
    WeakInductionConjugateInverseSelfDualTCStatement.{uV, uE, uE'} := by
  intro hRig E E' _ _ _ _ _ _ _ _ ξ r c hξ hc
  exact isConjugateSelfDual_of_isWeakAutomorphicInductionOf_of_isConjugateInverse
    (hRig.2.2 E) hξ hc

end Langlands.Global.Harris

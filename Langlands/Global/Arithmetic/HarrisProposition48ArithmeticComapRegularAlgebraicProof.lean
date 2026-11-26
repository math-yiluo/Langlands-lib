import Langlands.Automorphic.RegularAlgebraicArithmeticTransport
import Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement

/-! # Arithmetic pullback of regular algebraicity for the Harris singleton child -/

noncomputable section

universe uK uE

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- Regular algebraicity of an actual irreducible cuspidal realization passes to its
arithmetic pullback along an isomorphism of number fields, at independent field
universes. -/
theorem arithmeticComapRegularAlgebraic :
    ArithmeticComapRegularAlgebraicStatement.{uK, uE} := by
  intro K E _ _ _ _ _ _ e r S hS
  exact (S.arithmeticComap_isoClass_isRegularAlgebraic_iff e).mpr hS

end Langlands.Global.Harris

import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement
import Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceStatement
import Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement
import Langlands.Global.Arithmetic.CyclicNormKernelUnramifiedOrderStatement

/-! # Reduction of cyclic regular induction to existence and spectral comparison -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global.HeckeCharacter (CyclicNormKernelUnramifiedOrderStatement)

/-- Actual cuspidal induction existence, the exact local norm-character order,
and Euler constituent recovery imply the published regular induction target. -/
def CyclicRegularInductionReductionStatement : Prop :=
  CyclicRegularInductionExistenceStatement.{uF, uE, uV, uW} →
  CyclicNormKernelUnramifiedOrderStatement.{uF, uE} →
  CuspidalEulerConstituentRecoveryStatement.{uF, uV} →
  CyclicRegularInductionStatement.{uF, uE, uV, uW}

/-- Regular induction over a totally complex base uses the corresponding
existence and Euler recovery premises over totally complex fields. -/
def CyclicRegularInductionReductionTCStatement : Prop :=
  CyclicRegularInductionExistenceTCStatement.{uF, uE, uV, uW} →
  CyclicNormKernelUnramifiedOrderStatement.{uF, uE} →
  CuspidalEulerConstituentRecoveryTCStatement.{uF, uV} →
  CyclicRegularInductionTCStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified

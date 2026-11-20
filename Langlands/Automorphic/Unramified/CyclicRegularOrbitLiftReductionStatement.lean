import Langlands.Automorphic.Unramified.CyclicOrbitInductionComparisonStatement
import Langlands.Automorphic.Unramified.CyclicRegularInductionExistenceStatement
import Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangePairMultiplicityStatement

/-! # Reduction of regular orbit lifting to induction existence and pair multiplicities -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

/-- Actual cuspidal induction existence, the forward weak induction comparison,
and the norm-twist pair count imply the published regular orbit-lift target. -/
def CyclicRegularOrbitLiftReductionStatement : Prop :=
  CyclicRegularInductionExistenceStatement.{uF, uE, uV, uW} →
  WeakInductionOrbitBaseChangeStatement.{uF, uE, uV, uW} →
  CyclicWeakBaseChangePairMultiplicityStatement.{uF, uE, uV, uW} →
  CyclicRegularOrbitLiftStatement.{uF, uE, uV, uW}

/-- The regular orbit-lift reduction specialized to the totally complex inputs. -/
def CyclicRegularOrbitLiftReductionTCStatement : Prop :=
  CyclicRegularInductionExistenceTCStatement.{uF, uE, uV, uW} →
  WeakInductionOrbitBaseChangeStatement.{uF, uE, uV, uW} →
  CyclicWeakBaseChangePairMultiplicityTCStatement.{uF, uE, uV, uW} →
  CyclicRegularOrbitLiftTCStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified

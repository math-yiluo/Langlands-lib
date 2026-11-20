import Langlands.Automorphic.HeckeDeterminantTwistDualitySupercuspidalStatement
import Langlands.Automorphic.HeckeDeterminantTwistWeakInductionStatement
import Langlands.Global.Arithmetic.HarrisParityArithmeticTransportStatement
import Langlands.Global.Arithmetic.HarrisParityLocalTransportStatement
import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryInputStatement
import Langlands.Global.Arithmetic.HarrisProposition48ParityStatement

/-! # Reductions for the four Proposition 4.8 parity obligations -/

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- Arithmetic and finite-place transport suffice for the one-place
correction, using the published CM half-weight character construction. -/
def Proposition48AuxiliaryParityNormalizationReductionStatement : Prop :=
  NormTwistInfinityStatement.{0} →
  CMNormConjugationStatement.{0, 0} →
  Proposition48PlaceNormTwistStatement.{uF} →
  GeneralPositionAmbientTwistStatement.{uF} →
  Proposition48AuxiliaryParityNormalizationStatement.{uF}

/-- An auxiliary correction extends to the complete datum by transporting
the primary component using the same base character. -/
def Proposition48ParityNormalizationReductionStatement : Prop :=
  Proposition48AuxiliaryParityNormalizationStatement.{uF} →
  Proposition48PlaceNormTwistStatement.{uF} →
  Proposition48ParityNormalizationStatement.{uF}

/-- The three actual twist compatibilities suffice to untwist at the
auxiliary place. -/
def Proposition48AuxiliaryParityUntwistReductionStatement : Prop :=
  HeckeDeterminantTwistWeakInductionStatement.{0, uV} →
  HeckeDeterminantTwistConjugateSelfDualStatement.{0} →
  HeckeDeterminantTwistSupercuspidalStatement.{0, uV} →
  Proposition48AuxiliaryParityUntwistStatement.{uF, uV}

/-- The two-place untwist follows by projecting to the auxiliary datum. -/
def Proposition48ParityUntwistReductionStatement : Prop :=
  Proposition48AuxiliaryParityUntwistStatement.{uF, uV} →
  Proposition48ParityUntwistStatement.{uF, uV}

end Langlands.Global.Harris

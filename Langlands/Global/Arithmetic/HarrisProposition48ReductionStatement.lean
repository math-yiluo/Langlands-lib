import Langlands.Global.Arithmetic.HarrisProposition48MackeyStepStatement
import Langlands.Global.Arithmetic.HarrisProposition48PrimeBranchStatement
import Langlands.Global.Arithmetic.HarrisProposition48SingletonBranchStatement

/-! # Explicit-input reduction of Harris's Proposition 4.8 -/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic.Unramified Langlands.GaloisRepresentation

/-- The one-place induction and its named arithmetic and automorphic inputs
imply the unchanged Proposition 4.8 at the universes used by globalization. -/
def Proposition48ReductionStatement : Prop :=
  (Proposition48AuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48PrimeBranchStatement.{uF, uV} ∧
    Proposition48SingletonBranchStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} ∧
    HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} ∧
    CuspidalSpectralRigidityStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceStatement.{uV} ∧
    CyclicRegularInductionStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV}) →
  Proposition48Statement.{uF, 0, 0, 0, uV}

end Langlands.Global.Harris

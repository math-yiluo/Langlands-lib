import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData

/-! # Base case and parity inputs for the one-place induction -/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic LocalFactor.CommonClosure

/-- Hecke-character realization at rank one, using only the auxiliary place. -/
def Proposition48AuxiliaryRankOneStatement : Prop :=
  ∀ Q : Proposition48Problem.{uF}, Q.IsAuxiliaryValid →
    Module.finrank Q.E Q.E' = 1 → Q.HasSolution.{uF, uV}

/-- Correct the inherited parity by a genuine conjugate-inverse base character. -/
def Proposition48AuxiliaryParityNormalizationStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (b : ℕ), Q.IsAuxiliaryValidAtParity b →
    ∃ (ν : HeckeCharacter Q.E) (χs : FieldCharacter Q.F Q.F'),
      Q.IsAuxiliaryParityNormalization b ν χs

/-- Untwist a supplied corrected solution on actual cuspidal realizations. -/
def Proposition48AuxiliaryParityUntwistStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
    (χs : FieldCharacter Q.F Q.F'), Q.IsAuxiliaryValidAtParity b →
    Q.IsAuxiliaryParityNormalization b ν χs →
    ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
      (Q.withCharacters (Q.correctedCharacter ν) χs χs).IsSolution.{uF, uV} c →
      ∃ S T : CuspidalOperatorRealization Q.E r,
        T.isoClass = c ∧ Q.IsUntwistedSolution.{uF, uV} ν S T

/-- The base case and two separate parity obligations for internal induction. -/
def Proposition48AuxiliaryPreparationStatement : Prop :=
  Proposition48AuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV}

end Langlands.Global.Harris

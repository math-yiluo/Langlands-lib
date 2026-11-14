import Langlands.Global.Arithmetic.HarrisProposition48ParityData

/-! # Named parity-correction and untwisting inputs for Proposition 4.8 -/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic LocalFactor.CommonClosure

/-- A CM base character corrects the inherited infinity parity while
preserving the complete arithmetic setup and local general position. -/
def Proposition48ParityNormalizationStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (b : ℕ), Q.IsValidAtParity b →
    ∃ (ν : HeckeCharacter Q.E) (χ χs : FieldCharacter Q.F Q.F'),
      Q.IsParityNormalization b ν χ χs

/-- A solution for the normalized character can be untwisted through
genuine determinant multiplication, retaining the raw character and place. -/
def Proposition48ParityUntwistStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
    (χ χs : FieldCharacter Q.F Q.F'), Q.IsValidAtParity b →
    Q.IsParityNormalization b ν χ χs →
    ∀ (r : ℕ) (c : CuspidalOperatorRealization.IsoClass Q.E r),
      (Q.withCharacters (Q.correctedCharacter ν) χ χs).IsSolution.{uF, uV} c →
      ∃ S T : CuspidalOperatorRealization Q.E r,
        T.isoClass = c ∧ Q.IsUntwistedSolution.{uF, uV} ν S T

/-- The two distinct parity obligations, collected as one focused proof target. -/
def Proposition48ParityTransportStatement : Prop :=
  Proposition48ParityNormalizationStatement.{uF} ∧
    Proposition48ParityUntwistStatement.{uF, uV}

end Langlands.Global.Harris

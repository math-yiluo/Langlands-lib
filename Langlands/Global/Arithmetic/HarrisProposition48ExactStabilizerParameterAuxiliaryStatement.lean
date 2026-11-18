import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData

/-!
# Rank one and untwisting of complex-place parameters in Proposition 4.8

Two auxiliary statements for the exact-stabilizer form of the induction for
Harris (1998), Proposition 4.8, in which solutions carry the complex-place
parameters of the induced representation. At rank one, a solution with these
parameters exists. Untwisting a parity-normalized solution keeps these
parameters: the untwisted constituent has the parameters induced from the
original character. Proposition definitions only.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic LocalFactor.CommonClosure

/-- Rank one: a problem with the published one-place validity and
`[E' : E] = 1` has a solution with the complex-place parameters of `ξ`. -/
def Proposition48ExactStabilizerAuxiliaryRankOneStatement : Prop :=
  ∀ Q : Proposition48Problem.{uF}, Q.IsAuxiliaryValid →
    Module.finrank Q.E Q.E' = 1 → Q.HasParameterSolution.{uF, uV}

/-- Untwisting keeps the parameters. For a parity normalization `ν`, `χs` of a
problem `Q` at parity `b` and an untwisted solution `S`, `T` of `Q`: if `T` has
the complex-place parameters induced from the corrected character, then `S` has
those induced from the character of `Q`. -/
def Proposition48ExactStabilizerParameterUntwistStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
    (χs : FieldCharacter Q.F Q.F'), Q.IsAuxiliaryValidAtParity b →
    Q.IsAuxiliaryParityNormalization b ν χs →
    ∀ (r : ℕ) (S T : CuspidalOperatorRealization Q.E r),
      Q.IsUntwistedSolution.{uF, uV} ν S T →
      (Q.withCharacters (Q.correctedCharacter ν) χs χs).HasInducedComplexPlaceParameters
          T.isoClass →
        Q.HasInducedComplexPlaceParameters S.isoClass

end Langlands.Global.Harris

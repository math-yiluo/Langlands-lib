import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerData

/-!
# Inheritance of the exact Weil stabilizer condition in the Proposition 4.8 induction

Two statements saying that Harris's condition (4.12) (proof of Lemma 4.7,
Harris 1998, page 204) on the auxiliary character passes, in the Library's
induction for Proposition 4.8, from a problem to each of its Mackey children
and to its parity-corrected problem. In both, the published general-position
validity of the new problem is a hypothesis, and the conclusion upgrades it
to exact-stabilizer validity. Neither statement is proved here.
-/

noncomputable section

universe uF

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic LocalFactor.CommonClosure

/-- Condition (4.12) passes to Mackey children. Let `Q` satisfy the one-place
exact-stabilizer hypotheses at parity `b`, and let `R` be a Mackey child of
`Q` for an intermediate field `D` of `L/E` and an `E`-automorphism `a` of `L`.
If `R` satisfies the published one-place hypotheses at parity `c`, then `R`
satisfies the exact-stabilizer hypotheses at parity `c`. The field `D` is
arbitrary, not only a cyclic step of prime degree. -/
def Proposition48ExactStabilizerMackeyInheritanceStatement : Prop :=
  ∀ (Q R : Proposition48Problem.{uF}) (b c : ℕ) (D : IntermediateField Q.E Q.L)
    (a : Q.L ≃ₐ[Q.E] Q.L),
    Q.IsAuxiliaryExactStabilizerValidAtParity b →
    Q.IsAuxiliaryMackeyChild D a R →
    R.IsAuxiliaryValidAtParity c →
    R.IsAuxiliaryExactStabilizerValidAtParity c

/-- Condition (4.12) passes to the parity-corrected problem. Let `Q` satisfy
the one-place exact-stabilizer hypotheses at parity `b`, and let the base
character `ν` with the new auxiliary character `χs` be a parity normalization
of `Q` in the published sense (which includes the published one-place
validity of the corrected problem). Then the corrected problem satisfies the
one-place exact-stabilizer hypotheses at the original rank parity. -/
def Proposition48ExactStabilizerParityInheritanceStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (b : ℕ) (ν : HeckeCharacter Q.E)
    (χs : FieldCharacter Q.F Q.F'),
    Q.IsAuxiliaryExactStabilizerValidAtParity b →
    Q.IsAuxiliaryParityNormalization b ν χs →
    (Q.withCharacters (Q.correctedCharacter ν) χs χs).IsAuxiliaryExactStabilizerValid

end Langlands.Global.Harris

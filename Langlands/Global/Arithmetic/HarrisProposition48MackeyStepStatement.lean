import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData

/-! # A compatible arithmetic step in the Proposition 4.8 induction -/

noncomputable section

universe uF

namespace Langlands.Global.Harris

/-- Choose one compatible prime cyclic step together with all its actual
raw children, at inherited parity and smaller normal-closure degree. -/
def Proposition48MackeyStepStatement : Prop :=
  ∀ Q : Proposition48Problem.{uF}, Q.IsAuxiliaryValid →
    1 < Module.finrank Q.E Q.E' →
    ∃ D : IntermediateField Q.E Q.L,
      Q.IsPrimeCyclicStep D ∧
      (Nat.card (Q.MackeyIndex D) = 1 ∨
        Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D) ∧
      ∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ R : Proposition48Problem.{uF},
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree

end Langlands.Global.Harris

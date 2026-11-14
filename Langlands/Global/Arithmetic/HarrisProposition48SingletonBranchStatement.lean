import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryInputStatement
import Langlands.Global.Arithmetic.HarrisProposition48IsobaricInvarianceStatement
import Langlands.Galois.Harris1998ExistenceStatement
import Langlands.Automorphic.Unramified.CyclicTransferStatement

/-! # The singleton branch of Harris's Proposition 4.8 -/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.GaloisRepresentation LocalFactor.CommonClosure

/-- Select the correct cyclic descent of an actual singleton Mackey
constituent, with the foundational existence and rigidity inputs explicit. -/
def Proposition48SingletonBranchStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicStableDescentStatement.{0, 0, uV, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = 1 →
      (∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T) →
      Q.HasSolution.{uF, uV}

end Langlands.Global.Harris

import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryInputStatement
import Langlands.Global.Arithmetic.HarrisProposition48IsobaricInvarianceStatement
import Langlands.Galois.Harris1998ExistenceStatement
import Langlands.Galois.HarrisSupercuspidalLocalComparisonStatement
import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement
import Langlands.Automorphic.Unramified.CyclicWeakInductionSupercuspidalStatement

/-! # The prime-orbit branch of Harris's Proposition 4.8 -/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.GaloisRepresentation LocalFactor.CommonClosure

/-- Assemble actual raw Mackey constituents in a prime orbit. Foundational
inputs and all parity transport data are explicit hypotheses. -/
def Proposition48PrimeBranchStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityStatement.{0, uV} →
  Proposition48IsobaricInvarianceStatement.{uV} →
  CyclicRegularInductionStatement.{0, 0, uV, uV} →
  CyclicRegularOrbitLiftStatement.{0, 0, uV, uV} →
  CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D →
      Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
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

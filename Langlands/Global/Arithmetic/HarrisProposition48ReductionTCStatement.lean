import Langlands.Global.Arithmetic.HarrisProposition48ReductionStatement
import Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement
import Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement

/-!
# Harris's Proposition 4.8 from its named inputs, over totally complex fields

`Proposition48ReductionStatement` with its global automorphic inputs replaced by their totally
complex forms: Harris's input 9 (`CuspidalSpectralRigidityStatement`) and inputs 11–14 (the
cyclic transfer statements) by the forms with `[NumberField.IsTotallyComplex F]` inserted
after `[NumberField F]`; and inputs 5, 6 and 10, which take inputs 9–14 as hypotheses, by the
forms whose hypotheses are those totally complex forms (input 10 also restricts its number
field `K` by `[NumberField.IsTotallyComplex K]`). Inputs 1–4, 7 and 8 and the conclusion
`Proposition48Statement` are unchanged; universes are the same. Proposition definitions only.
See the paired Markdown for the reason (Harris's Proposition 4.8 concerns CM fields, and its
proof applies the inputs only over CM fields and their finite extensions, all totally
complex) and the sources.
-/

noncomputable section

universe uF uV

namespace Langlands.Global.Harris

section IsobaricInvariance

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Unramified

/-- The totally complex form of `Proposition48IsobaricInvarianceStatement`: totally complex
constituent rigidity upgrades equality of supplied Euler systems over a totally complex
number field `K` to Galois invariance of the actual isobaric multiset. -/
def Proposition48IsobaricInvarianceTCStatement : Prop :=
  CuspidalSpectralRigidityTCStatement.{0, uV} →
    ∀ (F K : Type) [Field F] [Field K] [NumberField K]
      [NumberField.IsTotallyComplex K] [Algebra F K]
      [CompactSpace (AdeleQuotient K)] (σ : K ≃ₐ[F] K) (D : IsobaricData K)
      (s : SpectralSystem (FinitePlace K) D.rank)
      (t : SpectralSystem (FinitePlace K) (D.galoisConj σ).rank),
      D.HasSpectralSystem.{0, uV} s →
      (D.galoisConj σ).HasSpectralSystem.{0, uV} t →
      s.SameEulerPolynomials t → D.IsGaloisStable σ

end IsobaricInvariance

section Branches

open Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.GaloisRepresentation LocalFactor.CommonClosure

/-- The totally complex form of `Proposition48PrimeBranchStatement`: the prime-orbit branch of
Harris's Proposition 4.8, with the global inputs rigidity, isobaric invariance and the three
cyclic inputs replaced by their totally complex forms; Harris's Theorem 1.2 and the
supercuspidal local comparison (stated for CM fields) and the body are unchanged. -/
def Proposition48PrimeBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicRegularInductionTCStatement.{0, 0, uV, uV} →
  CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} →
  CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV} →
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

/-- The totally complex form of `Proposition48SingletonBranchStatement`: the singleton branch
of Harris's Proposition 4.8, with rigidity, isobaric invariance and stable cyclic descent
replaced by their totally complex forms; Harris's Theorem 1.2 and the body are unchanged. -/
def Proposition48SingletonBranchTCStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
  CyclicStableDescentTCStatement.{0, 0, uV, uV} →
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

end Branches

section Reduction

open Langlands.Automorphic.Unramified Langlands.GaloisRepresentation

/-- The totally complex form of `Proposition48ReductionStatement`: the one-place induction
and its named arithmetic and automorphic inputs, with inputs 5, 6 and 9–14 in their totally
complex forms, imply the unchanged Proposition 4.8 at the universes used by
globalization. -/
def Proposition48ReductionTCStatement : Prop :=
  (Proposition48AuxiliaryRankOneStatement.{uF, uV} ∧
    Proposition48AuxiliaryParityNormalizationStatement.{uF} ∧
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} ∧
    Proposition48MackeyStepStatement.{uF} ∧
    Proposition48PrimeBranchTCStatement.{uF, uV} ∧
    Proposition48SingletonBranchTCStatement.{uF, uV} ∧
    Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} ∧
    HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} ∧
    CuspidalSpectralRigidityTCStatement.{0, uV} ∧
    Proposition48IsobaricInvarianceTCStatement.{uV} ∧
    CyclicRegularInductionTCStatement.{0, 0, uV, uV} ∧
    CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV} ∧
    CyclicStableDescentTCStatement.{0, 0, uV, uV} ∧
    CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV}) →
  Proposition48Statement.{uF, 0, 0, 0, uV}

end Reduction

end Langlands.Global.Harris

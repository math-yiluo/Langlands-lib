import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Galois.CompatibleFamily
import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryData

/-! # Rank, parity and auxiliary fields in the Harris singleton case -/

noncomputable section

universe uF uV uK uE

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.GaloisRepresentation LocalFactor.CommonClosure
open AdelicFunctoriality
open NumberField (IsCMField IsTotallyReal IsTotallyComplex maximalRealSubfield)

/-- The actual singleton child has parent rank. Its inherited parity correction
is the trivial character, so the raw child is the supplied regular algebraic
solution. -/
def Proposition48SingletonChildNormalizationStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
    ∀ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
      (χs : FieldCharacter R.F R.F') (r : ℕ) (S T : CuspidalOperatorRealization R.E r),
      Q.IsAuxiliaryMackeyChild D 1 R → Module.finrank R.E R.E' = Q.mackeyRank D 1 →
      R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs →
      R.IsUntwistedSolution.{uF, uV} ν S T →
      Module.finrank R.E R.E' = Module.finrank Q.E Q.E' ∧ ν = 1 ∧
      S.isoClass = T.isoClass ∧ R.IsSolution.{uF, uV} S.isoClass

/-- Infinitesimal regular algebraicity is invariant under arithmetic pullback
of the actual cuspidal realization along a field isomorphism. -/
def ArithmeticComapRegularAlgebraicStatement : Prop :=
  ∀ (K : Type uK) (E : Type uE) [Field K] [NumberField K] [Field E] [NumberField E]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient E)]
    (e : K ≃+* E) (r : ℕ) (S : CuspidalOperatorRealization E r),
    S.isoClass.IsRegularAlgebraic → (S.arithmeticComap e).isoClass.IsRegularAlgebraic

/-- The actual auxiliary place in the step field and its conjugate are the
unique places above the two specified base places. -/
def Proposition48AuxiliaryStepPlacesStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L) [IsCMField D],
    Q.IsAuxiliaryValid →
    ∀ w : FinitePlacesAbove D Q.Ps.v,
      ∃ wc : FinitePlacesAbove D (conjPlace Q.E Q.Ps.v),
        wc.val = conjPlace D w.val ∧ (∀ w', w' = w) ∧ (∀ w', w' = wc)

/-- The auxiliary-valid datum supplies the CM compositum and the prime split
in its imaginary quadratic field, in the form used by Theorem 1.2. -/
def Proposition48AuxiliaryTheorem12FieldStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}), Q.IsAuxiliaryValid →
    ∃ E₀ : IntermediateField ℚ Q.E,
      E₀.toSubfield = maximalRealSubfield Q.E ∧ IsTotallyReal E₀ ∧
      Module.finrank ℚ Q.K₀ = 2 ∧ IsTotallyComplex Q.K₀ ∧ E₀ ⊔ Q.K₀ = ⊤ ∧
      IsSplitImaginaryQuadratic (residueCharacteristic Q.Ps.v) Q.K₀

end Langlands.Global.Harris

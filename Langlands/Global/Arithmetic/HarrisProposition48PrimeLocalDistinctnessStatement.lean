import Langlands.Global.Arithmetic.HarrisProposition48PrimeOrbitBasepointStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData
import Langlands.Galois.HarrisSupercuspidalLocalComparisonStatement
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Global.AdeleQuotientCompactProof

/-! # The actual local witnesses for the general-position prime orbit -/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.GaloisRepresentation
open LocalFactor.CommonClosure NumberField AdelicFunctoriality

/-- The raw powers of the cyclic generator have pairwise distinct actual
supercuspidal components at the unique place, beginning with the supplied
basepoint component. The global basepoint is free under the nonidentity
powers used in cyclic induction. -/
def Proposition48PrimeLocalDistinctnessStatement : Prop :=
  HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV} →
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D →
    Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D →
    ∀ (σ : D ≃ₐ[Q.E] D), (∀ τ : D ≃ₐ[Q.E] D, τ ∈ Subgroup.zpowers σ) →
    ∀ (w : FinitePlacesAbove D Q.Ps.v), (∀ z : FinitePlacesAbove D Q.Ps.v, z = w) →
    ∀ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
      (χs : FieldCharacter R.F R.F') (r : ℕ)
      (S T : CuspidalOperatorRealization R.E r)
      (e : R.E ≃+* D) (e' : R.E' ≃+* Q.mackeyField D 1),
      Q.IsPrimeOrbitBasepoint D R w e e' →
      R.IsAuxiliaryValidAtParity (Module.finrank Q.E Q.E' - 1) →
      R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs →
      R.IsUntwistedSolution.{uF, uV} ν S T →
      letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
      ∀ (U : CuspidalOperatorRealization D r) (P : CuspidalSpectralPresentation.{0, uV} U),
        CuspidalOperatorRealization.IsArithmeticTransport e S U →
        Q.IsMackeyConstituent.{uF, uV} D 1 U.isoClass →
        (P.localComponent w.1).IsSupercuspidal →
        ∃ (V : Fin (Module.finrank Q.E D) → CuspidalOperatorRealization D r)
          (A : ∀ i, CuspidalSpectralPresentation.{0, uV} (V i)),
          (∀ i, U.isoClass.IsGaloisConjugate (σ ^ i.val) (V i).isoClass) ∧
          (∀ i, ((A i).localComponent w.1).IsSupercuspidal) ∧
          Function.Injective (fun i => ((A i).localComponent w.1).isoClass) ∧
          (∀ i, i.val = 0 →
            ((A i).localComponent w.1).isoClass = (P.localComponent w.1).isoClass) ∧
          (∀ i : ℕ, 0 < i → i < Module.finrank Q.E D →
            ¬ U.isoClass.IsGaloisStable (σ ^ i))

end Langlands.Global.Harris

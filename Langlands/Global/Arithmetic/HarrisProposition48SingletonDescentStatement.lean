import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerParameterData
import Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement
import Langlands.Galois.Harris1998ExistenceStatement

/-! # Statements for the singleton orbit of Harris's Proposition 4.8 -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField Langlands.Automorphic Langlands.Automorphic.Unramified
open Langlands.GaloisRepresentation Langlands.LocalFactor.Archimedean AdelicFunctoriality

def Proposition48SingletonMackeyGaloisStableTCStatement : Prop :=
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  Proposition48IsobaricInvarianceTCStatement.{uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      IsNormalClosure Q.E Q.E' Q.L → Nat.card (Q.MackeyIndex D) = 1 →
      letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
      ∀ (r : ℕ) (S : CuspidalOperatorRealization D r),
        Q.IsMackeyConstituent.{uF, uV} D 1 S.isoClass →
        ∀ σ : D ≃ₐ[Q.E] D, S.isoClass.IsGaloisStable σ

def WeakBaseChangeUnitaryCentralCharacterStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E r),
    ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW}
      T.isoClass S.isoClass →
    ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S

def Proposition48SingletonInducedParameterStatement : Prop :=
  ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
    IsNormalClosure Q.E Q.E' Q.L → Nat.card (Q.MackeyIndex D) = 1 →
    letI : Algebra D (Q.mackeyField D 1) :=
      (IntermediateField.inclusion (show D ≤ Q.mackeyField D 1 from le_sup_left)).toAlgebra
    ∀ (v : {v : InfinitePlace Q.E // v.IsComplex}) (w : InfinitePlacesAbove D v.1)
      (ds : List ComplexCharacterData) (d : ℕ)
      (e : Fin d ≃ InfinitePlacesAbove (Q.mackeyField D 1) (complexPlaceAbove v w).1)
      (dξ : InfinitePlacesAbove (Q.mackeyField D 1) (complexPlaceAbove v w).1 →
        ComplexCharacterData),
      (∀ w', (Q.mackeyCharacter D 1).HasComplexPlaceParameter
        (complexPlaceAbove (complexPlaceAbove v w) w') (dξ w')) →
      ds.Perm (complexPlaceLanglandsSum (complexPlaceAbove v w) e fun w' => [dξ w']) →
      Q.IsInducedComplexPlaceParameter v (complexPlaceParameterTransport v w ds)

def Proposition48SingletonDescentSelectionTCStatement : Prop :=
  Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV} →
  CuspidalSpectralRigidityTCStatement.{0, uV} →
  CyclicStableDescentTCStatement.{0, 0, uV, uV} →
    ∀ (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L),
      Q.IsAuxiliaryValid → Q.IsPrimeCyclicStep D → Nat.card (Q.MackeyIndex D) = 1 →
      letI : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
      ∀ [IsCMField D] (r : ℕ) (S : CuspidalOperatorRealization D r),
        ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
        S.isoClass.IsConjugateSelfDual →
        Q.IsMackeyConstituent.{uF, uV} D 1 S.isoClass →
        (∀ σ : D ≃ₐ[Q.E] D, S.isoClass.IsGaloisStable σ) →
        (∀ c : CuspidalOperatorRealization.IsoClass Q.E r,
          CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV}
            S.isoClass c →
          c.IsRegularAlgebraic ∧ c.HasSupercuspidalComponent.{0, uV} Q.Ps.v) →
        ∃ c : CuspidalOperatorRealization.IsoClass Q.E r,
          CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{0, 0, uV, uV}
            S.isoClass c ∧
          c.IsWeakAutomorphicInductionOf.{0, 0, uV} Q.ξ

end Langlands.Global.Harris

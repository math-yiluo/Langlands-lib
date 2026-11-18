import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport
import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Mathlib.FieldTheory.Galois.Basic

noncomputable section
universe uF uE uV uW
set_option autoImplicit false

namespace Langlands.Automorphic.Unramified
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.LocalFactor.Archimedean

/-- Complex-place compatibility for cyclic weak transfers. -/
def CyclicWeakBaseChangeComplexPlaceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
      (∀ (r : ℕ) (S : CuspidalOperatorRealization F r)
        (T : CuspidalOperatorRealization E r),
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
        IsoClass.IsWeakBaseChangeOf.{uF,uE,uV,uW} T.isoClass S.isoClass →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (w : InfinitePlacesAbove E v.1) (ds : List ComplexCharacterData),
          S.isoClass.HasComplexPlaceParameter v ds ↔
            T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w)
              (complexPlaceParameterTransport v w ds)) ∧
      (∀ (r m : ℕ) (S : CuspidalOperatorRealization F r)
        (T : CuspidalOperatorRealization E m),
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
        (∀ σ : E ≃ₐ[F] E, σ ≠ 1 → ¬ T.isoClass.IsGaloisStable σ) →
        IsoClass.IsWeakInductionOf.{uF,uE,uV,uW} S.isoClass T.isoClass →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (d : ℕ) (e : Fin d ≃ InfinitePlacesAbove E v.1)
          (ds : InfinitePlacesAbove E v.1 → List ComplexCharacterData),
          (∀ w, T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w) (ds w)) →
          S.isoClass.HasComplexPlaceParameter v (complexPlaceLanglandsSum v e ds)) ∧
      (∀ (DF : IsobaricData F) (DE : IsobaricData E),
        DF.IsUnitary → DE.IsUnitary →
        IsobaricData.IsWeakBaseChangeOf.{uF,uE,uV,uW} DE DF →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (w : InfinitePlacesAbove E v.1) (ds : List ComplexCharacterData),
          DF.HasComplexPlaceParameter v ds ↔
            DE.HasComplexPlaceParameter (complexPlaceAbove v w)
              (complexPlaceParameterTransport v w ds))

/-- The totally complex specialization of complex-place compatibility. -/
def CyclicWeakBaseChangeComplexPlaceTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
      (∀ (r : ℕ) (S : CuspidalOperatorRealization F r)
        (T : CuspidalOperatorRealization E r),
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
        IsoClass.IsWeakBaseChangeOf.{uF,uE,uV,uW} T.isoClass S.isoClass →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (w : InfinitePlacesAbove E v.1) (ds : List ComplexCharacterData),
          S.isoClass.HasComplexPlaceParameter v ds ↔
            T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w)
              (complexPlaceParameterTransport v w ds)) ∧
      (∀ (r m : ℕ) (S : CuspidalOperatorRealization F r)
        (T : CuspidalOperatorRealization E m),
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
        (∀ σ : E ≃ₐ[F] E, σ ≠ 1 → ¬ T.isoClass.IsGaloisStable σ) →
        IsoClass.IsWeakInductionOf.{uF,uE,uV,uW} S.isoClass T.isoClass →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (d : ℕ) (e : Fin d ≃ InfinitePlacesAbove E v.1)
          (ds : InfinitePlacesAbove E v.1 → List ComplexCharacterData),
          (∀ w, T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w) (ds w)) →
          S.isoClass.HasComplexPlaceParameter v (complexPlaceLanglandsSum v e ds)) ∧
      (∀ (DF : IsobaricData F) (DE : IsobaricData E),
        DF.IsUnitary → DE.IsUnitary →
        IsobaricData.IsWeakBaseChangeOf.{uF,uE,uV,uW} DE DF →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (w : InfinitePlacesAbove E v.1) (ds : List ComplexCharacterData),
          DF.HasComplexPlaceParameter v ds ↔
            DE.HasComplexPlaceParameter (complexPlaceAbove v w)
              (complexPlaceParameterTransport v w ds))

end Langlands.Automorphic.Unramified

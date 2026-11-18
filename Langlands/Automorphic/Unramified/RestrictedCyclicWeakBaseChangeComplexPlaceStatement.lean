import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.ArchimedeanPlaceParameterClasses
import Langlands.Global.Arithmetic.HarrisSetup
import Mathlib.FieldTheory.Galois.Basic

noncomputable section
universe uF uE uV uW
set_option autoImplicit false

namespace Langlands.Automorphic.Unramified
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.LocalFactor.Archimedean

/-- Restricted complex-place compatibility for cuspidal cyclic weak transfers. -/
def RestrictedCyclicWeakBaseChangeComplexPlaceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsCMField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (v₀ : Langlands.Global.FinitePlace F), v₀ ≠ Harris.conjPlace F v₀ →
    ∀ (w₀ : FinitePlacesAbove E v₀)
      (wc : FinitePlacesAbove E (Harris.conjPlace F v₀)),
      (∀ w', w' = w₀) → (∀ w', w' = wc) →
      (∀ (r : ℕ) (S : CuspidalOperatorRealization F r)
        (T : CuspidalOperatorRealization E r),
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
        S.isoClass.HasSupercuspidalComponent.{uF,uV} v₀ →
        S.isoClass.HasSupercuspidalComponent.{uF,uV} (Harris.conjPlace F v₀) →
        T.isoClass.HasSupercuspidalComponent.{uE,uW} w₀.1 →
        T.isoClass.HasSupercuspidalComponent.{uE,uW} wc.1 →
        IsoClass.IsWeakBaseChangeOf.{uF,uE,uV,uW} T.isoClass S.isoClass →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (w : InfinitePlacesAbove E v.1) (ds : List ComplexCharacterData),
          S.isoClass.HasComplexPlaceParameter v ds ↔
            T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w)
              (complexPlaceParameterTransport v w ds)) ∧
      (∀ (r m : ℕ) (S : CuspidalOperatorRealization F r)
        (T : CuspidalOperatorRealization E m),
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
        S.isoClass.HasSupercuspidalComponent.{uF,uV} v₀ →
        S.isoClass.HasSupercuspidalComponent.{uF,uV} (Harris.conjPlace F v₀) →
        T.isoClass.HasSupercuspidalComponent.{uE,uW} w₀.1 →
        T.isoClass.HasSupercuspidalComponent.{uE,uW} wc.1 →
        (∀ σ : E ≃ₐ[F] E, σ ≠ 1 → ¬ T.isoClass.IsGaloisStable σ) →
        IsoClass.IsWeakInductionOf.{uF,uE,uV,uW} S.isoClass T.isoClass →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (d : ℕ) (e : Fin d ≃ InfinitePlacesAbove E v.1)
          (ds : InfinitePlacesAbove E v.1 → List ComplexCharacterData),
          (∀ w, T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w) (ds w)) →
          S.isoClass.HasComplexPlaceParameter v (complexPlaceLanglandsSum v e ds))

end Langlands.Automorphic.Unramified

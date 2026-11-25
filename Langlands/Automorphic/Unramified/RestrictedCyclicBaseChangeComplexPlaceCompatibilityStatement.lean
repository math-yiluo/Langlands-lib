import Langlands.Automorphic.Unramified.CyclicTransferStatement
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport
import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Global.Arithmetic.HarrisSetup
import Mathlib.FieldTheory.Galois.Basic

noncomputable section
universe uF uE uV uW
set_option autoImplicit false

namespace Langlands.Automorphic.Unramified
open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.LocalFactor.Archimedean

/-- Restricted complex-place strong lifting for a cuspidal source and isobaric target. -/
def RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement : Prop :=
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
      ∀ (r : ℕ) (S : CuspidalOperatorRealization F r) (D : IsobaricData E),
        ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
        S.isoClass.HasSupercuspidalComponent.{uF,uV} v₀ →
        S.isoClass.HasSupercuspidalComponent.{uF,uV} (Harris.conjPlace F v₀) →
        D.IsUnitary →
        IsobaricData.IsWeakBaseChangeOf.{uF,uE,uV,uW} D
          (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass)) →
        ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
          (w : InfinitePlacesAbove E v.1) (ds : List ComplexCharacterData),
          IsobaricData.HasComplexPlaceParameter
              (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank S.isoClass))
              v ds ↔
            D.HasComplexPlaceParameter (complexPlaceAbove v w)
              (complexPlaceParameterTransport v w ds)

end Langlands.Automorphic.Unramified

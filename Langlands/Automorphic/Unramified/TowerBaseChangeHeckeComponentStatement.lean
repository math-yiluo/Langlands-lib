import Langlands.Automorphic.Unramified.HeckeFamilyEndpoint
import Langlands.Automorphic.Unramified.CyclicTransferStatement

noncomputable section

universe uF uK uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic.CuspidalOperatorRealization

/-- Standard B6 for supplied unitary isobaric chains. -/
def TowerBaseChangeHeckeComponentStatement : Prop :=
  ∀ (F : Type uF) (K : Type uK) [Field F] [NumberField F]
    [Field K] [NumberField K] [Algebra F K]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
    (T : PrimeCyclicBaseChangeTower F K)
    [∀ i, CompactSpace (AdeleQuotient (T.level i))]
    (D D' : T.IsobaricChain),
    D.IsUnitary → D'.IsUnitary →
    D.IsSuccessiveWeakBaseChange.{uF,uK,uV,uW} →
    D'.IsSuccessiveWeakBaseChange.{uF,uK,uV,uW} →
    ∀ (r : ℕ) (S S' : CuspidalOperatorRealization F r),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S' →
      D.StartsAtCuspidal S.isoClass → D'.StartsAtCuspidal S'.isoClass →
      ∀ (μ μ' : Fin (r + 1) → HeckeCharacter K),
        (∀ i, (μ i).IsUnitary) → (∀ i, (μ' i).IsUnitary) →
        D.EndsAtHeckeFamily.{uF,uK,uV} μ →
        D'.EndsAtHeckeFamily.{uF,uK,uW} μ' →
        ∀ (v : FinitePlace F) (w : FinitePlacesAbove K v),
          (∀ w' : FinitePlacesAbove K v, w' = w) →
          ¬ HeckeFamily.SameFiniteComponentsAt μ μ' w.1 →
          ∀ (P : CuspidalSpectralPresentation.{uF,uV} S)
            (P' : CuspidalSpectralPresentation.{uF,uW} S'),
            (P.localComponent v).isoClass ≠ (P'.localComponent v).isoClass

/-- The totally complex specialization of standard B6. -/
def TowerBaseChangeHeckeComponentTCStatement : Prop :=
  ∀ (F : Type uF) (K : Type uK) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F]
    [Field K] [NumberField K] [Algebra F K]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
    (T : PrimeCyclicBaseChangeTower F K)
    [∀ i, CompactSpace (AdeleQuotient (T.level i))]
    (D D' : T.IsobaricChain),
    D.IsUnitary → D'.IsUnitary →
    D.IsSuccessiveWeakBaseChange.{uF,uK,uV,uW} →
    D'.IsSuccessiveWeakBaseChange.{uF,uK,uV,uW} →
    ∀ (r : ℕ) (S S' : CuspidalOperatorRealization F r),
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
      ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S' →
      D.StartsAtCuspidal S.isoClass → D'.StartsAtCuspidal S'.isoClass →
      ∀ (μ μ' : Fin (r + 1) → HeckeCharacter K),
        (∀ i, (μ i).IsUnitary) → (∀ i, (μ' i).IsUnitary) →
        D.EndsAtHeckeFamily.{uF,uK,uV} μ →
        D'.EndsAtHeckeFamily.{uF,uK,uW} μ' →
        ∀ (v : FinitePlace F) (w : FinitePlacesAbove K v),
          (∀ w' : FinitePlacesAbove K v, w' = w) →
          ¬ HeckeFamily.SameFiniteComponentsAt μ μ' w.1 →
          ∀ (P : CuspidalSpectralPresentation.{uF,uV} S)
            (P' : CuspidalSpectralPresentation.{uF,uW} S'),
            (P.localComponent v).isoClass ≠ (P'.localComponent v).isoClass

end Langlands.Automorphic.Unramified

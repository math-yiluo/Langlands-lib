import Langlands.Automorphic.Unramified.IsobaricWeakTransfer

/-! # Transitivity and equivariance of attached weak base change -/

noncomputable section

universe uF uK uE uV uM uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global

/-- Weak base change of actual isobaric data composes in a tower, allowing
independent factor universes at its three fields. -/
def IsobaricWeakBaseChangeTowerStatement : Prop :=
  ∀ (F : Type uF) (K : Type uK) (E : Type uE)
    [Field F] [NumberField F] [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
    [CompactSpace (AdeleQuotient E)]
    (DF : IsobaricData F) (DK : IsobaricData K) (DE : IsobaricData E),
    IsobaricData.IsWeakBaseChangeOf.{uF, uK, uV, uM} DK DF →
    IsobaricData.IsWeakBaseChangeOf.{uK, uE, uM, uW} DE DK →
    IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF

/-- Weak base change of actual isobaric data is equivariant under compatible
automorphisms, acting by inverse arithmetic pullback on every constituent. -/
def IsobaricWeakBaseChangeEquivarianceStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (τF : F ≃+* F) (τE : E ≃+* E),
    (∀ x : F, τE (algebraMap F E x) = algebraMap F E (τF x)) →
    ∀ (DF : IsobaricData F) (DE : IsobaricData E),
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF →
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
        (DE.map fun c => c.arithmeticComap τE.symm)
        (DF.map fun c => c.arithmeticComap τF.symm)

end Langlands.Automorphic.Unramified

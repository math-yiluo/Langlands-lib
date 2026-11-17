import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement

noncomputable section
universe uF uE uV uW
set_option autoImplicit false
namespace Langlands.Automorphic.Unramified
open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization

/-- Arthur--Clozel III.4.2(c) restricted to totally complex F. -/
def CyclicPrimeIsobaricBaseChangeTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ DF : IsobaricData F, DF.IsUnitary →
      ∃ DE : IsobaricData E, DE.IsUnitary ∧
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF ∧
        ∀ DE' : IsobaricData E, DE'.IsUnitary →
          IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE' DF → DE' = DE


end Langlands.Automorphic.Unramified

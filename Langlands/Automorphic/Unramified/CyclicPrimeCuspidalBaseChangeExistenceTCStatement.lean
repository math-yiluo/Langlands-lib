import Langlands.Automorphic.Unramified.IsobaricWeakTransfer

/-! # Existence of weak base change for a single unitary cusp over a totally complex base -/

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global

/-- The existence consequence of Arthur–Clozel III.4.2(a) and (b) for one unitary cuspidal
class over a totally complex number field, with actual unitary isobaric data over `E`. -/
def CyclicPrimeCuspidalBaseChangeExistenceTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ c : PositiveRankCuspidalClass F, (IsobaricData.ofCuspidal c).IsUnitary →
      ∃ DE : IsobaricData E, DE.IsUnitary ∧
        IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE (IsobaricData.ofCuspidal c)

end Langlands.Automorphic.Unramified

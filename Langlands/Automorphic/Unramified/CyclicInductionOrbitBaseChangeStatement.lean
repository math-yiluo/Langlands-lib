import Langlands.Automorphic.Unramified.IsobaricWeakTransfer

/-! # Weak base change of a prime-degree weak induction -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global
open CuspidalOperatorRealization

/-- In the prime-degree cyclic case, the actual conjugate isobaric orbit
weakly base changes from a supplied cuspidal weak induction. -/
def CyclicInductionOrbitBaseChangeStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank F E).Prime →
    ∀ (r m : ℕ) (c : IsoClass F r) (d : IsoClass E m),
      IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c d →
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
        (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank d))
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c))

end Langlands.Automorphic.Unramified

import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement

/-! # Comparing weak induction with the weak base change to a full Galois orbit -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization

/-- The full Galois orbit of an upper cuspidal class is a weak base change
of every lower cuspidal class weakly induced from it. -/
def WeakInductionOrbitBaseChangeStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    {r m : ℕ} (c : IsoClass F r) (d : IsoClass E m),
    IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c d →
    IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
      (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank d))
      (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c))

/-- For a cyclic extension, weak base change to the full upper orbit recovers
weak induction if the actual lower class is fixed by the norm-kernel twist. -/
def CyclicOrbitBaseChangeWeakInductionStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (η : HeckeCharacter F), η.HasNormKernel E →
    ∀ {r m : ℕ} (c : IsoClass F r) (d : IsoClass E m),
      IsoClass.IsFiniteOrderDeterminantTwist η c c →
      IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW}
        (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank d))
        (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c)) →
      IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c d

end Langlands.Automorphic.Unramified

import Langlands.Automorphic.Unramified.IsobaricWeakTransfer

/-! # Transitivity of arithmetic weak induction in towers -/

noncomputable section

universe uF uK uE uV uM uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization

/-- Weakly inducing through an intermediate number field gives weak induction
from the top field, with each of the three classes carrying genuine spectral data. -/
def WeakInductionTransitivityStatement : Prop :=
  ∀ (F : Type uF) (K : Type uK) (E : Type uE)
    [Field F] [NumberField F] [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]
    [CompactSpace (AdeleQuotient E)]
    {r s m : ℕ} (c : IsoClass F r) (b : IsoClass K s) (d : IsoClass E m),
    IsoClass.IsWeakInductionOf.{uF, uK, uV, uM} c b →
    IsoClass.IsWeakInductionOf.{uK, uE, uM, uW} b d →
    IsoClass.IsWeakInductionOf.{uF, uE, uV, uW} c d

end Langlands.Automorphic.Unramified

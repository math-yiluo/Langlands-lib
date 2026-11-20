import Langlands.Automorphic.CuspidalSpectralDeterminantTwist
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Automorphic.Unramified.WeakTransfer
import Langlands.Global.HeckeCharacterFiniteOrder

/-! # Determinant twists in a weak base-change fibre -/

noncomputable section

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization

/-- An actual determinant twist by a character trivial on norms preserves
an attached weak base change. -/
def CuspidalWeakBaseChangeNormTwistStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (r : ℕ) (c c' : IsoClass F r) (d : IsoClass E r) (χ : HeckeCharacter F),
    χ.IsTrivialOnNorm E → IsoClass.IsFiniteOrderDeterminantTwist χ c c' →
    IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} d c →
    IsoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} d c'

/-- Arithmetic pullback of actual cuspidal classes transports the finite-order
determinant twist relation with the pullback of the character. -/
def CuspidalDeterminantTwistArithmeticComapStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]
    (e : F ≃+* E) (r : ℕ) (c c' : IsoClass E r) (χ : HeckeCharacter E),
    IsoClass.IsFiniteOrderDeterminantTwist χ c c' →
    IsoClass.IsFiniteOrderDeterminantTwist (HeckeCharacter.comap e χ)
      (c.arithmeticComap e) (c'.arithmeticComap e)

end Langlands.Automorphic.Unramified

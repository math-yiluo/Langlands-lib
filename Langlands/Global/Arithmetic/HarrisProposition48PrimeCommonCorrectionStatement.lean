import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.HeckeDeterminantTwistStatement
import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Automorphic.Unramified.WeakInduction
import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Global.AdelicFunctoriality.IdeleClassNorm

/-! # One parity correction on all the actual orbit presentations -/

noncomputable section

universe uK uL uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Unramified NumberField AdelicFunctoriality

/-- An actual normalized child can be pulled back along a field isomorphism
and corrected on the new base by another conjugate-inverse character of the
same parity. -/
def TransportedParityCorrectionStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K] [IsCMField K]
    [Field L] [NumberField L] [IsCMField L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (e : K ≃+* L) (b : ℕ) (ν : HeckeCharacter L) (η : HeckeCharacter K)
    (r : ℕ) (S T : CuspidalOperatorRealization L r),
    IsAlgebraicAfterTwist b ν → IsAlgebraicAfterTwist b η →
    IsConjugateInverse ν → IsConjugateInverse η →
    OperatorRealization.IsDeterminantMultiple ν S.realization T.realization →
    T.isoClass.IsRegularAlgebraic → T.isoClass.IsConjugateSelfDual →
    let U := (S.arithmeticComap e).heckeDeterminantTwist η
    U.isoClass.IsRegularAlgebraic ∧ U.isoClass.IsConjugateSelfDual

/-- The spectrum of the actual twisted presentation is weakly induced from
the inducing Hecke character times the norm pullback of the twist. -/
def WeakInductionDeterminantTwistStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (S : CuspidalOperatorRealization K r)
    (P : CuspidalSpectralPresentation.{uK, uV} S) (χ : HeckeCharacter L)
    (η : HeckeCharacter K),
    P.spectralSystem.IsWeakInductionOf χ →
      (P.heckeDeterminantTwist η).spectralSystem.IsWeakInductionOf
        (χ * η.comp (ideleClassNorm (K := K) (L := L)))

/-- Twisting the supplied presentation retains supercuspidality at its own
local component. -/
def CuspidalPresentationDeterminantTwistSupercuspidalStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (S : CuspidalOperatorRealization K r)
    (P : CuspidalSpectralPresentation.{uK, uV} S) (η : HeckeCharacter K)
    (v : FinitePlace K),
    (P.localComponent v).IsSupercuspidal →
      ((P.heckeDeterminantTwist η).localComponent v).IsSupercuspidal

/-- Inputs for applying a common correction to the actual raw conjugates
before the forward general-coefficient comparison. -/
def Proposition48PrimeCommonCorrectionStatement : Prop :=
  TransportedParityCorrectionStatement.{uK, uL} ∧
    WeakInductionDeterminantTwistStatement.{uK, uL, uV} ∧
    CuspidalPresentationDeterminantTwistSupercuspidalStatement.{uK, uV}

end Langlands.Global.Harris

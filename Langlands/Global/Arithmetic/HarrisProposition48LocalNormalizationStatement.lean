import Langlands.Automorphic.CentralCharacterTopCoefficient
import Langlands.Automorphic.FiniteLocalDeterminantTwist
import Langlands.Automorphic.HeckeDeterminantTwistStatement
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.Unramified.WeakInduction
import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Global.HeckeCharacterTransport

/-! # Actual rank-one components and integral determinant twists -/

noncomputable section

universe uK uA uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open Langlands.Automorphic Langlands.Unramified NumberField

/-- The degree-one case of weak induction recovers the transported Hecke
character on the actual center and on every embedded finite component. -/
def RankOneWeakInductionLocalStatement : Prop :=
  ∀ (K : Type uK) (A : Type uA) [Field K] [NumberField K]
    [Field A] [NumberField A] [Algebra K A] [CompactSpace (AdeleQuotient K)]
    (e : K ≃ₐ[K] A) (χ : HeckeCharacter A)
    (S : CuspidalOperatorRealization K 0) (P : CuspidalSpectralPresentation.{uK, uV} S),
    P.spectralSystem.IsWeakInductionOf χ →
    let δ := HeckeCharacter.comap e.toRingEquiv χ
    S.HasCentralCharacter δ ∧
      ∀ (v : FinitePlace K) (g : FiniteLocalGL K 1 v),
        (P.localComponent v).representation g =
          (δ.finiteLocalDeterminant 1 v g : ℂ) • LinearMap.id

/-- On the actual full operator realization, an integral infinity-type
determinant multiple preserves regular algebraicity. -/
def IntegralDeterminantTwistRegularAlgebraicStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [IsTotallyComplex K]
    (n : ℕ) (χ : HeckeCharacter K) (S T : OperatorRealization K n),
    IsAlgebraic χ → OperatorRealization.IsDeterminantMultiple χ S T →
      S.IsRegularAlgebraic → T.IsRegularAlgebraic

/-- The two normalization inputs for comparing actual prime-orbit constituents. -/
def Proposition48LocalNormalizationStatement : Prop :=
  RankOneWeakInductionLocalStatement.{uK, uA, uV} ∧
    IntegralDeterminantTwistRegularAlgebraicStatement.{uK}

end Langlands.Global.Harris

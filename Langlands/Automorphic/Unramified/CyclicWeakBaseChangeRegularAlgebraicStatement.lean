import Langlands.Automorphic.CuspidalComplexParameterBridgeStatement
import Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeComplexPlaceStatement

/-! # Regular algebraicity of a weak cyclic descent at a conjugate pair -/

noncomputable section

universe uK uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality

/-- Restricted complex-place compatibility and the infinitesimal-character
bridge give regular algebraicity of an actual weak descent when the upstairs
class is regular algebraic. The hypotheses retain the conjugate pair required
by restricted B7. -/
def CyclicWeakBaseChangeRegularAlgebraicTCStatement : Prop :=
  RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{uK, uE, uV, uW} →
  CuspidalComplexParameterBridgeTCStatement.{uK} →
  CuspidalComplexParameterBridgeTCStatement.{uE} →
  ∀ (K : Type uK) (E : Type uE) [Field K] [NumberField K] [NumberField.IsCMField K]
    [Field E] [NumberField E] [Algebra K E] [IsGalois K E] [IsCyclic (E ≃ₐ[K] E)]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient E)],
    (Module.finrank K E).Prime →
    ∀ (v₀ : FinitePlace K), v₀ ≠ Harris.conjPlace K v₀ →
    ∀ (w₀ : FinitePlacesAbove E v₀) (wc : FinitePlacesAbove E (Harris.conjPlace K v₀)),
      (∀ w', w' = w₀) → (∀ w', w' = wc) →
      ∀ (r : ℕ) (S : CuspidalOperatorRealization K r) (T : CuspidalOperatorRealization E r),
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter S →
        ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
        S.isoClass.HasSupercuspidalComponent.{uK, uV} v₀ →
        S.isoClass.HasSupercuspidalComponent.{uK, uV} (Harris.conjPlace K v₀) →
        T.isoClass.HasSupercuspidalComponent.{uE, uW} w₀.val →
        T.isoClass.HasSupercuspidalComponent.{uE, uW} wc.val →
        CuspidalOperatorRealization.IsoClass.IsWeakBaseChangeOf.{uK, uE, uV, uW}
          T.isoClass S.isoClass →
        T.isoClass.IsRegularAlgebraic → S.isoClass.IsRegularAlgebraic

end Langlands.Automorphic.Unramified

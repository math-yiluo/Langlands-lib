import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.CuspidalComplexParameterBridgeStatement
import Langlands.Automorphic.Unramified.CyclicPrimeIsobaricBaseChangeTCStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceStatement
import Langlands.Automorphic.Unramified.QuadraticWeakBaseChangeSplitSquareIntegrableStatement

/-! # The automorphic lift in the Harris parity argument -/

noncomputable section

universe uE uW

namespace Langlands.GaloisRepresentation

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Global
open Langlands.Global.AdelicFunctoriality Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- The weak automorphic lift to a quadratic CM extension at a split
square-integrable place is a conjugate self-dual regular algebraic cusp class. -/
def HarrisParityBaseChangeStatement : Prop :=
  CyclicPrimeIsobaricBaseChangeTCStatement.{uE, uE, uW, uW} →
  QuadraticWeakBaseChangeSplitSquareIntegrableStatement.{uE, uE, uW, uW} →
  CyclicWeakBaseChangeComplexPlaceTCStatement.{uE, uE, uW, uW} →
  CuspidalComplexParameterBridgeTCStatement.{uE} →
  ∀ (E N : Type uE) [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field N] [NumberField N] [NumberField.IsCMField N] [Algebra E N] [IsGalois E N]
    [CompactSpace (AdeleQuotient E)] [CompactSpace (AdeleQuotient N)],
    Module.finrank E N = 2 →
    ∀ (r : ℕ) (S : CuspidalOperatorRealization E r) (v : FinitePlace E),
      HasUnitaryCentralCharacter S → S.isoClass.IsRegularAlgebraic →
      S.isoClass.IsConjugateSelfDual →
      S.isoClass.HasSquareIntegrableComponent.{uE, uW} v → SplitsCompletelyAt (N := N) v →
      ∃ T : CuspidalOperatorRealization N r,
        T.isoClass.IsWeakBaseChangeOf.{uE, uE, uW, uW} S.isoClass ∧
        T.isoClass.IsRegularAlgebraic ∧ T.isoClass.IsConjugateSelfDual ∧
        ∀ w : FinitePlacesAbove N v, T.isoClass.HasSquareIntegrableComponent.{uE, uW} w.val

end Langlands.GaloisRepresentation

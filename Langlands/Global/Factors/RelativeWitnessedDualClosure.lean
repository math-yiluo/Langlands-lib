import Langlands.Global.Factors.RelativeDualWitnessedGenerator
import Langlands.Automorphic.AssociatedUnitaryCentralCharacter

/-! # Dual closure of actual relative witnessed generators -/

noncomputable section

universe uF uW uP

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global Langlands.Automorphic

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- Actual dual generators with exactly the two required local elements. -/
def RelativeWitnessedDualClosure : Prop :=
  ∀ d : WitnessedGenerator.{uF, uW, uP} F E c v,
    ∃ d' : WitnessedGenerator.{uF, uW, uP} F E c v,
      d'.weilElement = LocalWeil.unitaryDualLatticeEquiv (padicField v) d.weilElement ∧
        d'.automorphicElement =
          PadicSupercuspidal.unitaryContragredientLatticeEquiv
            (padicField v) d.automorphicElement

/-- Actual dual existence supplies closure once each original cuspidal
realization has a unitary central character and the four prerequisites hold. -/
theorem relativeWitnessedDualClosure_of_unitaryCentralCharacters
    (hcentral : ∀ d : WitnessedGenerator.{uF, uW, uP} F E c v,
      RelativeWeilGroup.HasUnitaryCentralCharacter d.cuspidal)
    (hex : CuspidalUnitaryContragredientExistenceStatement.{uF})
    (hpres : CuspidalContragredientPresentationExistenceStatement.{uF, uP, uP})
    (hlocal : CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uP})
    (hassoc : RelativeWeilGroup.PresentedContragredientAssociationStatement.{uF, uW, uP, uP}) :
    RelativeWitnessedDualClosure.{uF, uW, uP} F E c v := by
  intro d
  obtain ⟨d', _, hw, ha, _, _⟩ :=
    d.exists_dual (hcentral d) hex hpres hlocal hassoc
  exact ⟨d', hw, ha⟩

/-- The actual central-character comparison and arithmetic transfer discharge
all original unitary central-character witnesses in the dual-closure deduction.
The comparison and four contragredient proofs remain explicit inputs. -/
theorem relativeWitnessedDualClosure_of_centralComparison
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hcentral : RelativeWeilGroup.AssociatedCentralCharacterStatement.{uF, uW, uP})
    (hex : CuspidalUnitaryContragredientExistenceStatement.{uF})
    (hpres : CuspidalContragredientPresentationExistenceStatement.{uF, uP, uP})
    (hlocal : CuspidalContragredientLocalCompatibilityStatement.{uF, uP, uP})
    (hassoc : RelativeWeilGroup.PresentedContragredientAssociationStatement.{uF, uW, uP, uP}) :
    RelativeWitnessedDualClosure.{uF, uW, uP} F E c v := by
  apply relativeWitnessedDualClosure_of_unitaryCentralCharacters
    F E c v ?_ hex hpres hlocal hassoc
  intro d
  exact RelativeWeilGroup.hasUnitaryCentralCharacter_of_associatedCentralCharacter
    F E c hcentral hc d.weil d.cuspidal d.associatedClass d.weil_unitary

end Langlands.Global.PoleComparison

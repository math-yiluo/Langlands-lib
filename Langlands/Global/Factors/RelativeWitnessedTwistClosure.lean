import Langlands.Global.Factors.RelativeTwistWitnessedGenerator

/-! # Unitary twist closure of actual relative witnessed generators -/

noncomputable section

universe uF uW uP

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global Langlands.Automorphic

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)

/-- Every original witnessed generator has a generator with exactly the two
local unitary twists. This predicate does not assert the closure. -/
def RelativeWitnessedTwistClosure
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (χ : Correspondence.QuasiCharacter (padicField v))
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) : Prop :=
  ∀ d : WitnessedGenerator.{uF, uW, uP} F E c v,
    ∃ d' : WitnessedGenerator.{uF, uW, uP} F E c v,
      d'.weilElement =
          LocalWeil.unitaryFieldCharacterTwistLatticeEquiv
            (padicField v) e χ hχ d.weilElement ∧
        d'.automorphicElement =
          PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv
            (padicField v) χ hχ d.automorphicElement

/-- The actual global twist and local transfer statements, together with unitary
extension at the given field and place, supply every required twisted generator.
Each prerequisite remains a proof input of this intermediate deduction. -/
theorem relativeWitnessedTwistClosure_of_globalInputs
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hex : CuspidalDeterminantMultipleStatement.{uF, uP})
    (hassoc : RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement.{uF, uW, uP, uP})
    (htransfer : RelativeWeilGroup.LocalTransferReciprocityStatement.{uF})
    (hextend : ∀ η : (FiniteCompletion F v)ˣ →ₜ* ℂˣ,
      (∀ a, ‖(η a : ℂ)‖ = 1) →
      ∃ Ω : HeckeCharacter F, Ω.IsUnitary ∧ Ω.finiteComponent v = η)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (he : Correspondence.IsGeometricReciprocity (padicField v) e)
    (χ : Correspondence.QuasiCharacter (padicField v))
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) :
    RelativeWitnessedTwistClosure.{uF, uW, uP} F E c v e χ hχ := by
  intro d
  exact d.exists_unitaryCharacterTwist hc hex hassoc htransfer hextend e he χ hχ

end Langlands.Global.PoleComparison

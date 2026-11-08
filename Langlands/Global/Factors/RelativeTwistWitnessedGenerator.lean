import Langlands.VirtualRepresentation.Global.RelativeTwistedGenerator

/-! # Existence of actual relative generators after a unitary Hecke twist -/

noncomputable section

universe uF uW uP

set_option backward.isDefEq.respectTransparency false

namespace Langlands.VirtualRepresentation.RelativeGlobal.WitnessedGenerator

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality Langlands.Automorphic

variable {F E : Type uF} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  {c : FundamentalClass.ClassFamily.{uF}} {v : FinitePlace F}

/-- The actual determinant-multiple and association statements supply a complete
twisted generator with the two exact required local lattice elements. -/
theorem exists_heckeTwist
    (d : WitnessedGenerator.{uF, uW, uP} F E c v)
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hex : CuspidalDeterminantMultipleStatement.{uF, uP})
    (hassoc : RelativeWeilGroup.PresentedDeterminantMultipleAssociationStatement.{uF, uW, uP, uP})
    (htransfer : RelativeWeilGroup.LocalTransferReciprocityStatement.{uF})
    (Ω : HeckeCharacter F) (hΩ : Ω.IsUnitary)
    (e : Correspondence.ReciprocityCandidate (padicField v))
    (he : Correspondence.IsGeometricReciprocity (padicField v) e)
    (χ : Correspondence.QuasiCharacter (padicField v))
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (hΩv : ∀ a : (FiniteCompletion F v)ˣ, Ω.finiteComponent v a = χ a) :
    ∃ d' : WitnessedGenerator.{uF, uW, uP} F E c v,
      d'.weilElement =
          LocalWeil.unitaryFieldCharacterTwistLatticeEquiv
            (padicField v) e χ hχ d.weilElement ∧
        d'.automorphicElement =
          PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv
            (padicField v) χ hχ d.automorphicElement := by
  obtain ⟨T, P, hP⟩ := hex F d.cuspidal d.presentation Ω
  have ha := hassoc c hc F E d.weil d.cuspidal T d.presentation P Ω hP.1 d.associated
  let : d.placeOver.1.asIdeal.LiesOver v.asIdeal := d.placeOver.2
  have hι := htransfer c F E v d.placeOver.1 d.reciprocity d.localMap d.localMap_spec
  exact ⟨d.heckeTwist Ω χ hΩv T P hP hΩ e he hχ hι ha, rfl, rfl⟩

/-- Completion-topology unitary extension suffices for every canonical local
quasi-character in the operation target. -/
theorem exists_unitaryCharacterTwist
    (d : WitnessedGenerator.{uF, uW, uP} F E c v)
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
    ∃ d' : WitnessedGenerator.{uF, uW, uP} F E c v,
      d'.weilElement =
          LocalWeil.unitaryFieldCharacterTwistLatticeEquiv
            (padicField v) e χ hχ d.weilElement ∧
        d'.automorphicElement =
          PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv
            (padicField v) χ hχ d.automorphicElement := by
  let f : (FiniteCompletion F v)ˣ →* ℂˣ :=
    @ContinuousMonoidHom.toMonoidHom _ _ _ _
      (@Units.instTopologicalSpaceUnits _ (padicField v).canonicalTopologicalData.topology _)
      _ χ
  let η : (FiniteCompletion F v)ˣ →ₜ* ℂˣ :=
    { toMonoidHom := f
      continuous_toFun := by
        change @Continuous _ _
          (@Units.instTopologicalSpaceUnits _ (inferInstanceAs
            (TopologicalSpace (FiniteCompletion F v))) _) _ f
        rw [completion_topology_eq v]
        exact @ContinuousMonoidHom.continuous_toFun _ _ _ _
          (@Units.instTopologicalSpaceUnits _
            (padicField v).canonicalTopologicalData.topology _) _ χ }
  obtain ⟨Ω, hΩ, hΩv⟩ := hextend η (fun a => hχ a)
  exact d.exists_heckeTwist hc hex hassoc htransfer Ω hΩ e he χ hχ
    (fun a => DFunLike.congr_fun hΩv a)

section Choice

variable (d : WitnessedGenerator.{uF, uW, uP} F E c v)
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
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)

/-- Choose the complete generator whose existence was proved above. -/
def unitaryCharacterTwist : WitnessedGenerator.{uF, uW, uP} F E c v :=
  Classical.choose (d.exists_unitaryCharacterTwist hc hex hassoc htransfer hextend e he χ hχ)

@[simp]
theorem unitaryCharacterTwist_weilElement :
    (d.unitaryCharacterTwist hc hex hassoc htransfer hextend e he χ hχ).weilElement =
      LocalWeil.unitaryFieldCharacterTwistLatticeEquiv
        (padicField v) e χ hχ d.weilElement :=
  (Classical.choose_spec
    (d.exists_unitaryCharacterTwist hc hex hassoc htransfer hextend e he χ hχ)).1

@[simp]
theorem unitaryCharacterTwist_automorphicElement :
    (d.unitaryCharacterTwist hc hex hassoc htransfer hextend e he χ hχ).automorphicElement =
      PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv
        (padicField v) χ hχ d.automorphicElement :=
  (Classical.choose_spec
    (d.exists_unitaryCharacterTwist hc hex hassoc htransfer hextend e he χ hχ)).2

end Choice

end Langlands.VirtualRepresentation.RelativeGlobal.WitnessedGenerator

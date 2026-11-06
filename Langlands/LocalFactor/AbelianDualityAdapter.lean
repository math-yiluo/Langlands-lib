import Langlands.LocalFactor.CommonClosureNormCharacter
import Langlands.LocalFactor.NonabelianDualityAssembly

/-! # Scalar abelian duality and actual continuous character lines -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianSystem

open CommonClosure VirtualRepresentation

/-- The scalar fixed-Haar identity for the actual abelian expression on each
common-closure intermediate field. This isolates an analytic input; it is not
an added law of a nonabelian system. -/
def AbelianExpressionDualityStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : Extension F),
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (μ μ' : HaarMeasure F E),
      FourierDualMeasures F E ψ μ μ' → ∀ χ : FieldCharacter F E,
      (fieldData F E).abelianEpsilonExpression χ ψ μ *
        (fieldData F E).abelianEpsilonExpression
          ((fieldData F E).normalizedAbsCharacter * χ⁻¹) (ψ.scale (-1)) μ' = 1

/-- A scalar abelian dual-Haar equation gives the same equation on every
actual continuous Weil character, using genuine abelianization descent. -/
theorem characterLineDuality_of_abelianExpressionDuality
    (habelian : AbelianExpressionDualityStatement.{uF}) :
    CharacterLineDualityStatement.{uF, uV} := by
  intro p hp F e ε hε E ψ μ μ' hμ χ
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let c : (weilSubgroup F E →ₜ* ℂˣ) ≃ FieldCharacter F E :=
    LocalClassField.abelianizationLiftEquiv.trans
      (LocalClassField.characterTransport (e E))
  let η := c χ
  have hχ : weilCharacter F e E η = χ := c.symm_apply_apply χ
  have hclass : characterClass.{uF, uV} F e E η =
      ExactGrothendieckGroup.characterClass χ := by
    unfold characterClass
    rw [hχ]
  apply (mem_dualityKernel F ε hε.2.1 E ψ μ μ' _).mpr
  rw [← hclass]
  change ε E ψ μ (characterClass F e E η) *
    ε E (ψ.scale (-1)) μ'
      (ExactGrothendieckGroup.continuousTwistedDual
        (CommonClosureWeilDeligne.normCharacter F E)
        (characterClass F e E η)) = 1
  rw [normTwistedDual_characterClass F e hε.1 E η]
  apply Units.ext
  change (ε E ψ μ (characterClass F e E η) : ℂ) *
    (ε E (ψ.scale (-1)) μ'
      (characterClass F e E ((fieldData F E).normalizedAbsCharacter * η⁻¹)) : ℂ) = 1
  rw [hε.2.2.2.2 E η ψ μ,
    hε.2.2.2.2 E ((fieldData F E).normalizedAbsCharacter * η⁻¹) (ψ.scale (-1)) μ']
  exact habelian F E ψ μ μ' hμ η

/-- The scalar identity and actual degree-zero generation imply both published
functional equations. Both mathematical inputs remain explicit. -/
theorem dualFunctionalEquation_of_generation_of_abelianExpressionDuality
    (hgen : CommonClosureDegreeZeroGenerationStatement.{uF, uV})
    (habelian : AbelianExpressionDualityStatement.{uF}) :
    DualFunctionalEquationStatement.{uF, uV} :=
  dualFunctionalEquation_of_generation_of_characterLineDuality hgen
    (characterLineDuality_of_abelianExpressionDuality habelian)

end Langlands.LocalFactor.NonabelianSystem

import Langlands.LocalFactor.NonabelianBrauerPresentation
import Langlands.LocalFactor.NonabelianRankOneScaling
import Langlands.LocalFactor.NonabelianDeterminantTransfer
import Langlands.LocalFactor.NonabelianTraceScaling
import Langlands.LocalFactor.Inductive.GallagherDeterminantProof

/-! # Additive-character scaling before nonabelian descent -/

noncomputable section

universe uF uV

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "FieldCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
    (@borel F.Carrier T.topology)

/-- Fixed-Haar additive-character scaling for the actual epsilon unit. -/
theorem abelianEpsilonUnit_scale (χ : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.abelianEpsilonUnit χ (ψ.scale a) μ =
      T.abelianScalingFactor χ a * T.abelianEpsilonUnit χ ψ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply Units.ext
  exact T.abelianEpsilonExpression_scale_factor χ ψ μ a

/-- The absolute-value correction cancels in a character-difference ratio. -/
theorem abelianEpsilonRatio_scale (χ χ' : FieldCharacter)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (a : F.Carrierˣ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    T.abelianEpsilonRatio χ χ' (ψ.scale a) μ =
      (χ a / χ' a) * T.abelianEpsilonRatio χ χ' ψ μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [abelianEpsilonRatio, T.abelianEpsilonUnit_scale, T.abelianEpsilonUnit_scale,
    mul_div_mul_comm]
  have hfactor : T.abelianScalingFactor χ a / T.abelianScalingFactor χ' a =
      χ a / χ' a := by
    change (χ a * _⁻¹) / (χ' a * _⁻¹) = χ a / χ' a
    exact mul_div_mul_right_eq_div _ _ _
  rw [hfactor]
  rfl

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Evaluate the determinant of the actual presented virtual class at a Weil
element. This is independent of the expression of that class. -/
def determinantEvaluation (e : ReciprocityFamily F) (E : Extension F)
    (w : weilSubgroup F E) : Presentation F E →ₗ[ℤ] Additive ℂˣ :=
  ({ toFun z := Additive.ofMul
       (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E)
         (virtualPresentation F e E z) w)
     map_zero' := by
       simp only [map_zero]
       rfl
     map_add' z z' := by
       simp only [map_add, ExactGrothendieckGroup.determinantCharacter_add_apply]
       rfl } : Presentation F E →+ Additive ℂˣ).toIntLinearMap

@[simp]
theorem determinantEvaluation_single (e : ReciprocityFamily F) (E : Extension F)
    (w : weilSubgroup F E) (g : Generator F E) (n : ℤ) :
    determinantEvaluation.{uF, uV} F e E w (Finsupp.single g n) =
      n • Additive.ofMul
        (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E)
          (generatorClass.{uF, uV} F e E g) w) := by
  change Additive.ofMul
    (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E)
      (Finsupp.linearCombination ℤ _ (Finsupp.single g n)) w) = _
  rw [Finsupp.linearCombination_single,
    ExactGrothendieckGroup.determinantCharacter_zsmul_apply]
  exact ofMul_zpow _ _

/-- The determinant transfer formula identifies a generator's correction with
the ratio of its actual field-character values. -/
theorem determinant_generatorClass (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (g : Generator F E)
    (w : weilSubgroup F E) :
    ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate.{uF, uV} F E)
        (generatorClass F e E g) w =
      g.first (E.unitsInclusion g.extension g.inclusion (reciprocityUnits F e E w)) /
        g.second (E.unitsInclusion g.extension g.inclusion (reciprocityUnits F e E w)) := by
  let := (fieldData F g.extension).topology
  let z : DegreeZero.{uF, uV} F g.extension :=
    ⟨characterClass F e g.extension g.first - characterClass F e g.extension g.second,
      by
        change degree F g.extension _ = 0
        simp only [map_sub, degree_characterClass, sub_self]⟩
  obtain ⟨v, hv⟩ := exists_reciprocityUnits_eq F e g.extension
    (E.unitsInclusion g.extension g.inclusion (reciprocityUnits F e E w))
  have hdet := determinant_induce_degreeZero_reciprocity F
    Inductive.gallagherDeterminant e he E g.extension g.inclusion z w v hv
  change ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E)
      (induce F E g.extension g.inclusion z.val) w = _
  rw [hdet]
  change ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F g.extension)
    (characterClass F e g.extension g.first - characterClass F e g.extension g.second) v = _
  rw [ExactGrothendieckGroup.determinantCharacter_sub_apply,
    CommonClosure.determinantCharacter_characterClass,
    CommonClosure.determinantCharacter_characterClass]
  change g.first (reciprocityUnits F e g.extension v) /
    g.second (reciprocityUnits F e g.extension v) = _
  rw [hv]

/-- Trace pullback makes the scalar in each generator exactly the actual nested
field inclusion of the base scalar. -/
theorem generatorValue_scale (E : Extension F) (g : Generator F E) :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (measures : HaarFamily F) (a : E.fieldˣ),
      generatorValue F E (ψ.scale a) measures g =
        (g.first (E.unitsInclusion g.extension g.inclusion a) /
          g.second (E.unitsInclusion g.extension g.inclusion a)) *
            generatorValue F E ψ measures g := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let := (fieldData F g.extension).topology
  let := (fieldData F g.extension).valuativeRel
  let := (fieldData F g.extension).localField
  intro ψ measures a
  unfold generatorValue
  rw [traceCharacter_scale, PadicField.TopologicalData.abelianEpsilonRatio_scale]

/-- Deligne's additive-character scaling identity holds on the free presentation
before the arithmetic kernel identity is known. -/
theorem evaluationMap_scale (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (measures : HaarFamily F)
      (a : E.fieldˣ) (w : weilSubgroup F E),
      reciprocityUnits F e E w = a →
      evaluationMap F E (ψ.scale a) measures =
        determinantEvaluation.{uF, uV} F e E w + evaluationMap F E ψ measures := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  intro ψ measures a w ha
  apply Finsupp.lhom_ext
  intro g n
  simp only [LinearMap.add_apply, evaluationMap_single, determinantEvaluation_single]
  rw [generatorValue_scale]
  rw [determinant_generatorClass F e he, ha]
  rw [ofMul_mul, zsmul_add]

/-- For an actual presentation relation the determinant correction is trivial,
so its epsilon product is unchanged by scaling the additive character. -/
theorem evaluationMap_scale_of_presentationMap_eq_zero
    (e : ReciprocityFamily F) (he : NormalizedReciprocity F e) (E : Extension F) :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    ∀ (ψ : AdditiveCharacter F E) (measures : HaarFamily F) (a : E.fieldˣ)
      (z : Presentation F E),
      presentationMap.{uF, uV} F e E z = 0 →
      evaluationMap F E (ψ.scale a) measures z = evaluationMap F E ψ measures z := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  intro ψ measures a z hz
  obtain ⟨w, hw⟩ := exists_reciprocityUnits_eq F e E a
  rw [evaluationMap_scale F e he E ψ measures a w hw, LinearMap.add_apply]
  have hclass : virtualPresentation.{uF, uV} F e E z = 0 :=
    congrArg Subtype.val hz
  have hdet : determinantEvaluation.{uF, uV} F e E w z = 0 := by
    change Additive.ofMul
      (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E)
        (virtualPresentation F e E z) w) = 0
    rw [hclass, ExactGrothendieckGroup.determinantCharacter_zero_apply]
    rfl
  rw [hdet, zero_add]

end Langlands.LocalFactor.NonabelianBrauer

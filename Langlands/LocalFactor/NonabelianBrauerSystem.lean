import Langlands.LocalFactor.NonabelianBrauerDescent
import Langlands.LocalFactor.NonabelianBrauerNecessity
import Langlands.LocalFactor.CommonClosureCoherence

/-! # System laws for conditional actual Brauer descent -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable (e : ReciprocityFamily F) (hcompat : KernelCompatibility.{uF, uV} F e)
  (he : NormalizedReciprocity F e)

/-- Actual reduction fixes every class whose actual virtual degree is zero. -/
@[simp]
theorem reducedVirtual_degreeZero (E : Extension F) (x : DegreeZero.{uF, uV} F E) :
    reducedVirtual F e E x.val = x := by
  apply Subtype.ext
  have hx : degree F E x.val = 0 := x.property
  simp only [reducedVirtual_coe, hx, zero_smul, sub_zero]

/-- On the actual degree kernel the assignment is precisely the descended value,
computed with any family of regular Haar measures. -/
theorem assignment_degreeZero (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ : HaarMeasure F E) (measures : HaarFamily F) (x : DegreeZero.{uF, uV} F E) :
    assignment F e hcompat he E ψ μ x.val =
      Additive.toMul (degreeZeroValue F e hcompat he E ψ measures x) := by
  have hx : degree F E x.val = 0 := x.property
  rw [assignment_formula, hx, zpow_zero, mul_one, reducedVirtual_degreeZero,
    degreeZeroValue_haarIndependent F e hcompat he E ψ (referenceMeasures F) measures]

/-- Regard a generator over a nested field as a generator over the base field. -/
def Generator.over (E L : Extension F) (h : E.field ≤ L.field)
    (g : Generator F L) : Generator F E :=
  ⟨g.extension, le_trans h g.inclusion, g.first, g.second⟩

/-- A character difference over the same actual field has its abelian ratio. -/
theorem degreeZeroValue_characterDifference (E : Extension F)
    (χ η : FieldCharacter F E) (ψ : AdditiveCharacter F E) (measures : HaarFamily F) :
    degreeZeroValue F e hcompat he E ψ measures
      ⟨characterClass F e E χ - characterClass F e E η, by
        change degree F E _ = 0
        simp⟩ =
      Additive.ofMul ((fieldData F E).abelianEpsilonRatio χ η ψ (measures E)) := by
  have hg := degreeZeroValue_generator F e hcompat he E ψ measures
    (⟨E, le_rfl, χ, η⟩ : Generator F E)
  simpa only [generatorClass, generatorValue, induce_self, LinearMap.id_apply,
    traceCharacter_self] using hg

/-- The constructed assignment agrees with the actual abelian unit on every line. -/
theorem assignment_characterClass (E : Extension F) (χ : FieldCharacter F E)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    assignment F e hcompat he E ψ μ (characterClass F e E χ) =
      (fieldData F E).abelianEpsilonUnit χ ψ μ := by
  have hred : reducedVirtual F e E (characterClass F e E χ) =
      ⟨characterClass F e E χ - characterClass F e E 1, by
        change degree F E _ = 0
        simp⟩ := by
    apply Subtype.ext
    simp
  rw [assignment_formula, hred, degreeZeroValue_characterDifference,
    degree_characterClass, zpow_one]
  change (fieldData F E).abelianEpsilonRatio χ 1 ψ (referenceMeasures F E) *
    (fieldData F E).abelianEpsilonUnit 1 ψ μ = _
  rw [(fieldData F E).abelianEpsilonRatio_haarIndependent χ 1 ψ
    (referenceMeasures F E) μ]
  exact div_mul_cancel _ _

/-- Rank-one agreement has exactly the original complex-valued expression. -/
theorem assignment_rankOne :
    NonabelianSystem.RankOneRelation F e (assignment F e hcompat he) := by
  intro E χ ψ μ
  rw [assignment_characterClass, PadicField.TopologicalData.coe_abelianEpsilonUnit]

/-- Transitivity of actual induction carries the same source generator down
through an intermediate field. -/
theorem presentationMap_over (E L : Extension F) (h : E.field ≤ L.field)
    (g : Generator F L) :
    induceDegreeZero.{uF, uV} F E L h (presentationMap F e L (Finsupp.single g 1)) =
      presentationMap F e E (Finsupp.single (g.over F E L h) 1) := by
  apply Subtype.ext
  change induce F E L h (presentationMap F e L (Finsupp.single g 1)).val = _
  simp only [presentationMap_single, one_smul, generatorClass, Generator.over]
  rw [induce_trans]

/-- The abelian generator evaluation uses the same iterated trace character. -/
theorem generatorValue_over (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (measures : HaarFamily F) (g : Generator F L) :
    generatorValue F E ψ measures (g.over F E L h) =
      generatorValue F L (traceCharacter F E L h ψ) measures g := by
  simp only [generatorValue, Generator.over]
  rw [traceCharacter_trans]

/-- Descended degree-zero evaluation commutes with actual nested induction. -/
theorem degreeZeroValue_induce (E L : Extension F) (h : E.field ≤ L.field)
    (ψ : AdditiveCharacter F E) (measures : HaarFamily F) (x : DegreeZero.{uF, uV} F L) :
    degreeZeroValue F e hcompat he E ψ measures (induceDegreeZero F E L h x) =
      degreeZeroValue F e hcompat he L (traceCharacter F E L h ψ) measures x := by
  let A := (degreeZeroValue F e hcompat he E ψ measures).comp (induceDegreeZero F E L h)
  let B := degreeZeroValue F e hcompat he L (traceCharacter F E L h ψ) measures
  have hcomp : A.comp (presentationMap F e L) = B.comp (presentationMap F e L) := by
    apply Finsupp.lhom_ext
    intro g n
    have hs : Finsupp.single g n = n • Finsupp.single g 1 := by simp
    rw [hs]
    simp only [map_smul]
    congr 1
    change degreeZeroValue F e hcompat he E ψ measures
      (induceDegreeZero F E L h (presentationMap F e L (Finsupp.single g 1))) =
      degreeZeroValue F e hcompat he L (traceCharacter F E L h ψ) measures
        (presentationMap F e L (Finsupp.single g 1))
    rw [presentationMap_over, degreeZeroValue_presentation, degreeZeroValue_presentation,
      evaluationMap_single, evaluationMap_single, one_smul, one_smul, generatorValue_over]
  obtain ⟨z, rfl⟩ := presentationMap_surjective F e L x
  exact LinearMap.congr_fun hcomp z

/-- Degree-zero induction is independent of the arbitrary Haar measures on
both fields, as required by the original system law. -/
theorem assignment_induction :
    NonabelianSystem.InductionRelation F (assignment F e hcompat he) := by
  intro E L h ψ μ μL x
  change assignment F e hcompat he E ψ μ (induceDegreeZero F E L h x).val = _
  rw [assignment_degreeZero F e hcompat he E ψ μ (referenceMeasures F),
    assignment_degreeZero F e hcompat he L (traceCharacter F E L h ψ) μL (referenceMeasures F),
    degreeZeroValue_induce]

/-- A complete system on the unchanged actual objects, conditional only on the
explicit arithmetic kernel assertion and the existing reciprocity premise. -/
def system : { ε : NonabelianSystem.Assignment.{uF, uV} F // NonabelianSystem.IsSystem F e ε } :=
  ⟨assignment F e hcompat he, he, assignment_additive F e hcompat he,
    assignment_haarScaling F e hcompat he, assignment_induction F e hcompat he,
    assignment_rankOne F e hcompat he⟩

include hcompat in
/-- The arithmetic kernel assertion suffices for the unchanged existence target. -/
theorem exists_of_kernelCompatibility : NonabelianSystem.Exists.{uF, uV} F e := by
  intro hn
  exact ⟨(system F e hcompat hn).val, (system F e hcompat hn).property⟩

/-- On the unchanged conditional telescope, arithmetic kernel compatibility is
exactly the remaining obstruction to an actual full system. -/
theorem exists_iff_kernelCompatibility :
    NonabelianSystem.Exists.{uF, uV} F e ↔ KernelCompatibility.{uF, uV} F e :=
  ⟨kernelCompatibility_of_exists F e, fun h => exists_of_kernelCompatibility F e h⟩

/-- Specialize the universally quantified arithmetic assertion to this field,
without changing any field or representation universe. -/
theorem exists_of_kernelCompatibilityStatement
    (h : KernelCompatibilityStatement.{uF, uV}) :
    NonabelianSystem.Exists.{uF, uV} F e :=
  exists_of_kernelCompatibility F e (h p F e)

end Langlands.LocalFactor.NonabelianBrauer

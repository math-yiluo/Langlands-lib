import Langlands.LocalFactor.NonabelianBrauerKernelStatement
import Langlands.LocalFactor.CommonClosureSpectralGenerationReduction
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Descent conditional on the actual arithmetic kernel identity -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable (e : ReciprocityFamily F) (hcompat : KernelCompatibility.{uF, uV} F e)
  (he : NormalizedReciprocity F e)

include hcompat he in
/-- The displayed arithmetic assertion is precisely the needed kernel inclusion. -/
theorem presentation_ker_le_evaluation_ker (E : Extension F)
    (ψ : AdditiveCharacter F E) (measures : HaarFamily F) :
    LinearMap.ker (presentationMap.{uF, uV} F e E) ≤
      LinearMap.ker (evaluationMap F E ψ measures) :=
  fun _ hz => hcompat he E ψ measures _ hz

/-- Abelian evaluation descended to the actual continuous exact dimension kernel.
The arithmetic kernel assertion remains an explicit hypothesis. -/
def degreeZeroValue (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) : DegreeZero.{uF, uV} F E →ₗ[ℤ] Additive ℂˣ :=
  ((LinearMap.ker (presentationMap F e E)).liftQ (evaluationMap F E ψ measures)
      (presentation_ker_le_evaluation_ker F e hcompat he E ψ measures)).comp
    ((presentationMap F e E).quotKerEquivOfSurjective
      (presentationMap_surjective F e E)).symm.toLinearMap

/-- Descent recovers the actual abelian product on every finite presentation. -/
@[simp]
theorem degreeZeroValue_presentation (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (z : Presentation F E) :
    degreeZeroValue F e hcompat he E ψ measures (presentationMap F e E z) =
      evaluationMap F E ψ measures z := by
  simp only [degreeZeroValue, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

/-- In particular it has the prescribed value on each actual induced difference. -/
theorem degreeZeroValue_generator (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (g : Generator F E) :
    degreeZeroValue F e hcompat he E ψ measures
      ⟨generatorClass F e E g, generatorClass_mem_degreeZero F e E g⟩ =
      Additive.ofMul (generatorValue F E ψ measures g) := by
  have hg : presentationMap F e E (Finsupp.single g 1) =
      ⟨generatorClass F e E g, generatorClass_mem_degreeZero F e E g⟩ := by
    apply Subtype.ext
    simp
  rw [← hg, degreeZeroValue_presentation, evaluationMap_single, one_smul]

/-- The descended map is independent of the entire Haar family. -/
theorem degreeZeroValue_haarIndependent (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures measures' : HaarFamily F) :
    degreeZeroValue F e hcompat he E ψ measures =
      degreeZeroValue F e hcompat he E ψ measures' := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := presentationMap_surjective F e E x
  rw [degreeZeroValue_presentation, degreeZeroValue_presentation,
    evaluationMap_haarIndependent F E ψ measures measures']

/-- The interpolation condition determines the descended linear map uniquely. -/
theorem degreeZeroValue_unique (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (A : DegreeZero.{uF, uV} F E →ₗ[ℤ] Additive ℂˣ)
    (hA : ∀ z, A (presentationMap F e E z) = evaluationMap F E ψ measures z) :
    A = degreeZeroValue F e hcompat he E ψ measures := by
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ := presentationMap_surjective F e E x
  rw [hA, degreeZeroValue_presentation]

/-- A reference Haar family used only inside the measure-independent descent. -/
def referenceMeasures : HaarFamily F := fun E => Classical.choice (CommonClosureSpectralAnalytic.haarMeasure_nonempty (F := F) E)

/-- Subtract the actual degree times the trivial reciprocal character line. -/
def reducedVirtual (E : Extension F) : Virtual.{uF, uV} F E →ₗ[ℤ] DegreeZero F E :=
  (LinearMap.id - (degree F E).smulRight (characterClass F e E 1)).codRestrict
    (DegreeZero F E) fun x => by
      change degree F E (x - degree F E x • characterClass F e E 1) = 0
      simp

@[simp]
theorem reducedVirtual_coe (E : Extension F) (x : Virtual.{uF, uV} F E) :
    (reducedVirtual F e E x).val = x - degree F E x • characterClass F e E 1 := rfl

/-- Degree-zero descent and the abelian value on the trivial line define an
additive map on the entire original exact virtual group. -/
def virtualValue (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    Virtual.{uF, uV} F E →ₗ[ℤ] Additive ℂˣ :=
  (degreeZeroValue F e hcompat he E ψ (referenceMeasures F)).comp (reducedVirtual F e E) +
    (degree F E).smulRight (Additive.ofMul ((fieldData F E).abelianEpsilonUnit 1 ψ μ))

/-- The resulting actual unit-valued assignment. Its system laws still require
proof; arithmetic compatibility is not discharged by this construction. -/
def assignment : NonabelianSystem.Assignment.{uF, uV} F :=
  fun E ψ μ x => Additive.toMul (virtualValue F e hcompat he E ψ μ x)

/-- Integer linearity gives multiplicativity on the actual exact quotient. -/
theorem assignment_additive :
    NonabelianSystem.AdditiveRelation F (assignment F e hcompat he) := by
  intro E ψ μ x y
  exact congrArg Additive.toMul (map_add (virtualValue F e hcompat he E ψ μ) x y)

/-- The full value is the degree-zero value times the trivial-line value raised
to the actual integer virtual degree. -/
theorem assignment_formula (E : Extension F) (ψ : AdditiveCharacter F E)
    (μ : HaarMeasure F E) (x : Virtual.{uF, uV} F E) :
    assignment F e hcompat he E ψ μ x =
      Additive.toMul (degreeZeroValue F e hcompat he E ψ (referenceMeasures F)
        (reducedVirtual F e E x)) *
      (fieldData F E).abelianEpsilonUnit 1 ψ μ ^ degree F E x := rfl

/-- The constructed assignment satisfies the actual integer-degree Haar law. -/
theorem assignment_haarScaling :
    NonabelianSystem.HaarScalingRelation F (assignment F e hcompat he) := by
  intro E ψ μ c hc x
  rw [assignment_formula, assignment_formula]
  have hscale : (fieldData F E).abelianEpsilonUnit 1 ψ (scaleHaar F E μ c hc) =
      NonabelianSystem.positiveScale c hc * (fieldData F E).abelianEpsilonUnit 1 ψ μ := by
    exact (fieldData F E).abelianEpsilonUnit_haarScale 1 ψ μ c hc
  rw [hscale, mul_zpow]
  exact mul_left_comm _ _ _

end Langlands.LocalFactor.NonabelianBrauer

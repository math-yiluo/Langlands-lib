import Langlands.LocalFactor.CommonClosureGenerationProof
import Langlands.LocalFactor.Abelian.EpsilonUnit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Actual degree-zero Brauer presentations and abelian evaluation -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- A nested actual field and a pair of continuous field characters. -/
structure Generator (E : Extension F) where
  extension : Extension F
  inclusion : E.field ≤ extension.field
  first : FieldCharacter F extension
  second : FieldCharacter F extension

/-- Formal finite integer combinations of actual character differences. -/
abbrev Presentation (E : Extension F) := Generator F E →₀ ℤ

/-- The actual induced continuous exact virtual class of a generator. -/
def generatorClass (e : ReciprocityFamily F) (E : Extension F)
    (g : Generator F E) : Virtual.{uF, uV} F E :=
  induce F E g.extension g.inclusion
    (characterClass F e g.extension g.first - characterClass F e g.extension g.second)

/-- Every generator has actual virtual dimension zero. -/
theorem generatorClass_mem_degreeZero (e : ReciprocityFamily F) (E : Extension F)
    (g : Generator F E) : generatorClass.{uF, uV} F e E g ∈ DegreeZero F E := by
  change degree F E _ = 0
  rw [generatorClass, degree_induce, map_sub, degree_characterClass,
    degree_characterClass, sub_self, mul_zero]

/-- Converting field characters to Weil characters does not change the published
set of character-difference induction generators. -/
theorem generatorClass_range (e : ReciprocityFamily F) (E : Extension F) :
    Set.range (generatorClass.{uF, uV} F e E) =
      characterDifferenceInductionGenerators F E := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.extension, g.inclusion, weilCharacter F e g.extension g.first,
      weilCharacter F e g.extension g.second, rfl⟩
  · rintro ⟨L, h, χ, χ', rfl⟩
    let := (fieldData F L).topology
    let c : (weilSubgroup F L →ₜ* ℂˣ) ≃ FieldCharacter F L :=
      LocalClassField.abelianizationLiftEquiv.trans
        (LocalClassField.characterTransport (e L))
    have hχ : weilCharacter F e L (c χ) = χ := c.symm_apply_apply χ
    have hχ' : weilCharacter F e L (c χ') = χ' := c.symm_apply_apply χ'
    refine ⟨⟨L, h, c χ, c χ'⟩, ?_⟩
    change induce F E L h
      (ExactGrothendieckGroup.characterClass (weilCharacter F e L (c χ)) -
        ExactGrothendieckGroup.characterClass (weilCharacter F e L (c χ'))) = _
    rw [hχ, hχ']

/-- Sum the actual induced classes in the continuous exact virtual group. -/
def virtualPresentation (e : ReciprocityFamily F) (E : Extension F) :
    Presentation F E →ₗ[ℤ] Virtual.{uF, uV} F E :=
  Finsupp.linearCombination ℤ (generatorClass F e E)

/-- Published actual degree-zero generation identifies precisely the range. -/
theorem virtualPresentation_range (e : ReciprocityFamily F) (E : Extension F) :
    LinearMap.range (virtualPresentation.{uF, uV} F e E) = DegreeZero F E := by
  rw [virtualPresentation, Finsupp.range_linearCombination, generatorClass_range]
  exact commonClosureDegreeZeroGeneration p F E

/-- The same presentation with its actual dimension-zero codomain. -/
def presentationMap (e : ReciprocityFamily F) (E : Extension F) :
    Presentation F E →ₗ[ℤ] DegreeZero.{uF, uV} F E :=
  (virtualPresentation F e E).codRestrict (DegreeZero F E) fun z => by
    rw [← virtualPresentation_range F e E]
    exact LinearMap.mem_range_self _ z

/-- Every actual degree-zero class has a finite presentation. -/
theorem presentationMap_surjective (e : ReciprocityFamily F) (E : Extension F) :
    Function.Surjective (presentationMap.{uF, uV} F e E) := by
  intro x
  have hx : x.val ∈ LinearMap.range (virtualPresentation F e E) := by
    rw [virtualPresentation_range]
    exact x.property
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, Subtype.ext hz⟩

@[simp]
theorem presentationMap_single (e : ReciprocityFamily F) (E : Extension F)
    (g : Generator F E) (n : ℤ) :
    (presentationMap.{uF, uV} F e E (Finsupp.single g n)).val =
      n • generatorClass F e E g := by
  change Finsupp.linearCombination ℤ _ (Finsupp.single g n) = _
  exact Finsupp.linearCombination_single _ _ _

/-- A family of actual regular additive Haar measures, with no normalization. -/
abbrev HaarFamily := ∀ E : Extension F, HaarMeasure F E

/-- The actual abelian ratio of a generator, with trace-pulled additive character. -/
def generatorValue (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (g : Generator F E) : ℂˣ :=
  (fieldData F g.extension).abelianEpsilonRatio g.first g.second
    (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension)

/-- Multiplication of actual abelian ratios, written additively for integer
linear algebra. Zero in the codomain is the multiplicative unit. -/
def evaluationMap (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) : Presentation F E →ₗ[ℤ] Additive ℂˣ :=
  Finsupp.linearCombination ℤ (fun g => Additive.ofMul (generatorValue F E ψ measures g))

@[simp]
theorem evaluationMap_single (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (g : Generator F E) (n : ℤ) :
    evaluationMap F E ψ measures (Finsupp.single g n) =
      n • Additive.ofMul (generatorValue F E ψ measures g) :=
  Finsupp.linearCombination_single _ _ _

/-- The generator evaluation is independent of every supplied Haar measure. -/
theorem generatorValue_haarIndependent (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures measures' : HaarFamily F) (g : Generator F E) :
    generatorValue F E ψ measures g = generatorValue F E ψ measures' g :=
  (fieldData F g.extension).abelianEpsilonRatio_haarIndependent _ _ _ _ _

/-- This independence persists for every finite integer combination. -/
theorem evaluationMap_haarIndependent (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures measures' : HaarFamily F) :
    evaluationMap F E ψ measures = evaluationMap F E ψ measures' := by
  unfold evaluationMap
  congr 1
  funext g
  rw [generatorValue_haarIndependent F E ψ measures measures']

end Langlands.LocalFactor.NonabelianBrauer

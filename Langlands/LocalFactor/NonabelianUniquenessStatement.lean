import Langlands.LocalFactor.NonabelianSystem
import Langlands.LocalField.Topology

/-!
# The common-closure generation input for local-constant uniqueness

The generation and uniqueness assertions are proposition definitions.
The reduction proves uniqueness only from the displayed generation premise.
-/

noncomputable section

namespace Langlands.LocalFactor

open CommonClosure VirtualRepresentation

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Actual inductions of differences of continuous character lines from nested
finite intermediate fields of the one specified algebraic closure. -/
def characterDifferenceInductionGenerators (E : Extension F) :
    Set (Virtual.{uF, uV} F E) :=
  {x | ∃ (L : Extension F) (h : E.field ≤ L.field)
      (χ χ' : weilSubgroup F L →ₜ* ℂˣ),
    x = induce F E L h
      (ExactGrothendieckGroup.characterClass χ -
        ExactGrothendieckGroup.characterClass χ')}

/-- The degree-zero form of Tate's generation assertion on the actual
continuous exact virtual groups in one common closure. -/
def CommonClosureDegreeZeroGeneration : Prop :=
  ∀ E : Extension F,
    Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) =
      DegreeZero F E

/-- The common-closure generation assertion for every prime and finite p-adic
field, with an independent representation-carrier universe. -/
def CommonClosureDegreeZeroGenerationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    CommonClosureDegreeZeroGeneration.{uF, uV} F

/-- Uniqueness of local-constant assignments for the same supplied reciprocity
family and specified closure, for every finite p-adic field. -/
def NonabelianSystemUniquenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (e : ReciprocityFamily F),
    NonabelianSystem.Unique.{uF, uV} F e

/-- Every displayed generator has actual virtual dimension zero. -/
theorem characterDifferenceInductionGenerators_subset_degreeZero (E : Extension F) :
    characterDifferenceInductionGenerators.{uF, uV} F E ⊆ DegreeZero F E := by
  rintro x ⟨L, h, χ, χ', rfl⟩
  change degree F E _ = 0
  rw [degree_induce, map_sub, ExactGrothendieckGroup.degree_characterClass,
    ExactGrothendieckGroup.degree_characterClass, sub_self, mul_zero]

/-- The elementary inclusion needs no generation or Brauer theorem. -/
theorem span_characterDifferenceInductionGenerators_le (E : Extension F) :
    Submodule.span ℤ (characterDifferenceInductionGenerators.{uF, uV} F E) ≤
      DegreeZero F E :=
  Submodule.span_le.mpr (characterDifferenceInductionGenerators_subset_degreeZero F E)

namespace NonabelianSystem

private theorem haarMeasure_nonempty (E : Extension F) :
    Nonempty (HaarMeasure F E) := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  let : MeasurableSpace E.field := borel E.field
  let : BorelSpace E.field := ⟨rfl⟩
  let := (fieldData F E).fieldT2
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts E.field) := inferInstance
  exact ⟨HarmonicAnalysis.normalizedAdditiveHaar E.field K⟩

private def valueHom (ε : Assignment.{uF, uV} F) (hε : AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    Virtual.{uF, uV} F E →+ Additive ℂˣ where
  toFun x := Additive.ofMul (ε E ψ μ x)
  map_zero' := value_zero hε E ψ μ
  map_add' x y := hε E ψ μ x y

/-- Rank-one agreement compares the two systems on every continuous character
of the actual Weil subgroup, by genuine abelianization descent. -/
theorem IsSystem.eq_on_characterClass {e : ReciprocityFamily F}
    {ε₁ ε₂ : Assignment.{uF, uV} F}
    (h₁ : IsSystem F e ε₁) (h₂ : IsSystem F e ε₂)
    (E : Extension F) (χ : weilSubgroup F E →ₜ* ℂˣ)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    ε₁ E ψ μ (ExactGrothendieckGroup.characterClass χ) =
      ε₂ E ψ μ (ExactGrothendieckGroup.characterClass χ) := by
  let := (fieldData F E).topology
  let c : (weilSubgroup F E →ₜ* ℂˣ) ≃ FieldCharacter F E :=
    LocalClassField.abelianizationLiftEquiv.trans
      (LocalClassField.characterTransport (e E))
  let η := c χ
  have hχ : weilCharacter F e E η = χ := c.symm_apply_apply χ
  have hclass : characterClass.{uF, uV} F e E η =
      ExactGrothendieckGroup.characterClass χ := by
    unfold characterClass
    rw [hχ]
  apply Units.ext
  rw [← hclass]
  exact (h₁.2.2.2.2 E η ψ μ).trans (h₂.2.2.2.2 E η ψ μ).symm

/-- Degree-zero generation suffices for actual assignment uniqueness for a
fixed supplied reciprocity family; it is retained as an explicit premise. -/
theorem unique_of_commonClosureDegreeZeroGeneration
    (hgen : CommonClosureDegreeZeroGeneration.{uF, uV} F)
    (e : ReciprocityFamily F) : Unique.{uF, uV} F e := by
  intro ε₁ ε₂ h₁ h₂
  funext E ψ μ x
  let a := (valueHom F ε₁ h₁.2.1 E ψ μ).toIntLinearMap
  let b := (valueHom F ε₂ h₂.2.1 E ψ μ).toIntLinearMap
  have hchar (χ : weilSubgroup F E →ₜ* ℂˣ) :
      a (ExactGrothendieckGroup.characterClass χ) =
        b (ExactGrothendieckGroup.characterClass χ) :=
    congrArg Additive.ofMul (h₁.eq_on_characterClass F h₂ E χ ψ μ)
  have hgens : ∀ y ∈ characterDifferenceInductionGenerators.{uF, uV} F E,
      a y = b y := by
    rintro y ⟨L, h, χ, χ', rfl⟩
    obtain ⟨μL⟩ := haarMeasure_nonempty F L
    let z : DegreeZero.{uF, uV} F L :=
      ⟨ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ', by
        change degree F L _ = 0
        rw [map_sub, ExactGrothendieckGroup.degree_characterClass,
          ExactGrothendieckGroup.degree_characterClass, sub_self]⟩
    change Additive.ofMul (ε₁ E ψ μ (induce F E L h z.val)) =
      Additive.ofMul (ε₂ E ψ μ (induce F E L h z.val))
    rw [h₁.2.2.2.1 E L h ψ μ μL z, h₂.2.2.2.1 E L h ψ μ μL z]
    change valueHom F ε₁ h₁.2.1 L (traceCharacter F E L h ψ) μL
        (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ') =
      valueHom F ε₂ h₂.2.1 L (traceCharacter F E L h ψ) μL
        (ExactGrothendieckGroup.characterClass χ -
          ExactGrothendieckGroup.characterClass χ')
    rw [map_sub, map_sub]
    congr 1
    · exact congrArg Additive.ofMul
        (h₁.eq_on_characterClass F h₂ L χ (traceCharacter F E L h ψ) μL)
    · exact congrArg Additive.ofMul
        (h₁.eq_on_characterClass F h₂ L χ' (traceCharacter F E L h ψ) μL)
  have hker : DegreeZero.{uF, uV} F E ≤ LinearMap.ker (a - b) := by
    rw [← hgen E]
    apply Submodule.span_le.mpr
    intro y hy
    change a y - b y = 0
    exact sub_eq_zero.mpr (hgens y hy)
  let t : Virtual.{uF, uV} F E :=
    ExactGrothendieckGroup.characterClass (1 : weilSubgroup F E →ₜ* ℂˣ)
  let y := x - degree F E x • t
  have hyt : y ∈ DegreeZero.{uF, uV} F E := by
    change degree F E (x - degree F E x • t) = 0
    simp [t]
  have hy : a y = b y := by
    exact sub_eq_zero.mp (hker hyt)
  have ht : a t = b t := hchar 1
  have hdecomp : y + degree F E x • t = x := sub_add_cancel _ _
  have hx : a x = b x := by
    calc
      a x = a (y + degree F E x • t) := congrArg a hdecomp.symm
      _ = a y + degree F E x • a t := by rw [map_add, map_smul]
      _ = b y + degree F E x • b t := by rw [hy, ht]
      _ = b (y + degree F E x • t) := by rw [map_add, map_smul]
      _ = b x := congrArg b hdecomp
  exact congrArg Additive.toMul hx

end NonabelianSystem

/-- The all-field reduction retains the generation assertion as its premise. -/
theorem nonabelianSystemUniqueness_of_commonClosureDegreeZeroGeneration
    (hgen : CommonClosureDegreeZeroGenerationStatement.{uF, uV}) :
    NonabelianSystemUniquenessStatement.{uF, uV} := by
  intro p hp F e
  exact NonabelianSystem.unique_of_commonClosureDegreeZeroGeneration F (hgen p F) e

end Langlands.LocalFactor

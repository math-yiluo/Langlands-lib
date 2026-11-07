import Langlands.LocalFactor.NonabelianBrauerKernelStatement

/-! # The arithmetic kernel identity forced by an actual system -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An additive assignment is an integer-linear value map after writing
multiplication of complex units additively. -/
def systemValue (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.AdditiveRelation F ε)
    (E : Extension F) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    Virtual.{uF, uV} F E →ₗ[ℤ] Additive ℂˣ :=
  ({ toFun x := Additive.ofMul (ε E ψ μ x)
     map_zero' := NonabelianSystem.value_zero hε E ψ μ
     map_add' x y := hε E ψ μ x y } :
    Virtual.{uF, uV} F E →+ Additive ℂˣ).toIntLinearMap

/-- Rank-one agreement identifies the actual unit, not just its complex value. -/
theorem systemValue_characterClass (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (χ : FieldCharacter F E) (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) :
    systemValue F ε hε.2.1 E ψ μ (characterClass F e E χ) =
      Additive.ofMul ((fieldData F E).abelianEpsilonUnit χ ψ μ) := by
  change Additive.ofMul (ε E ψ μ (characterClass F e E χ)) = _
  apply congrArg Additive.ofMul
  apply Units.ext
  exact hε.2.2.2.2 E χ ψ μ

/-- Degree-zero induction and rank-one agreement determine every actual
generator value of a supplied full system. -/
theorem systemValue_generatorClass (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (measures : HaarFamily F) (g : Generator F E) :
    systemValue F ε hε.2.1 E ψ (measures E) (generatorClass F e E g) =
      Additive.ofMul (generatorValue F E ψ measures g) := by
  let x : DegreeZero.{uF, uV} F g.extension :=
    ⟨characterClass F e g.extension g.first -
        characterClass F e g.extension g.second, by
      change degree F g.extension _ = 0
      simp⟩
  change Additive.ofMul (ε E ψ (measures E)
    (induce F E g.extension g.inclusion x.val)) = _
  rw [hε.2.2.2.1 E g.extension g.inclusion ψ (measures E) (measures g.extension) x]
  change systemValue F ε hε.2.1 g.extension
    (traceCharacter F E g.extension g.inclusion ψ) (measures g.extension)
      (characterClass F e g.extension g.first -
        characterClass F e g.extension g.second) = _
  rw [map_sub, systemValue_characterClass F e ε hε,
    systemValue_characterClass F e ε hε]
  rfl

/-- The entire free epsilon evaluation is the restriction of a supplied full
system to its actual virtual presentation. -/
theorem evaluationMap_eq_systemValue_comp (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (measures : HaarFamily F) :
    evaluationMap F E ψ measures =
      (systemValue F ε hε.2.1 E ψ (measures E)).comp
        (virtualPresentation F e E) := by
  apply Finsupp.lhom_ext
  intro g n
  simp only [evaluationMap_single, LinearMap.comp_apply, virtualPresentation,
    Finsupp.linearCombination_single, map_smul, systemValue_generatorClass F e ε hε]

/-- Every actual full system forces precisely the published arithmetic kernel
assertion. This implication is a necessity result, not an existence proof. -/
theorem kernelCompatibility_of_system (e : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) :
    KernelCompatibility.{uF, uV} F e := by
  intro _ E ψ measures z hz
  have hv : virtualPresentation F e E z = 0 :=
    congrArg Subtype.val hz
  rw [evaluationMap_eq_systemValue_comp F e ε hε E ψ measures,
    LinearMap.comp_apply, hv, map_zero]

/-- The original conditional existence proposition implies arithmetic kernel
compatibility without any change of its normalized reciprocity premise. -/
theorem kernelCompatibility_of_exists (e : ReciprocityFamily F)
    (h : NonabelianSystem.Exists.{uF, uV} F e) :
    KernelCompatibility.{uF, uV} F e := by
  intro he
  obtain ⟨ε, hε⟩ := h he
  exact kernelCompatibility_of_system F e ε hε he

end Langlands.LocalFactor.NonabelianBrauer

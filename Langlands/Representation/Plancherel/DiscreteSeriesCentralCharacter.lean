import Langlands.Representation.Plancherel.DiscreteSeriesOrbitTopology
import Langlands.Representation.Category.ClassInvariants
import Langlands.Representation.Category.CentralCharacterRegularity
import Mathlib.Analysis.Complex.Circle

/-! # Actual unitary central characters of discrete-series classes -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Plancherel

universe uG uV uI uH

variable {G : Type uG} [Group G] [TopologicalSpace G]

private theorem centralCharacter_unique
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G))
    {c d : Subgroup.center G →* ℂˣ}
    (hc : SmoothDualClass.HasCentralCharacter c ω)
    (hd : SmoothDualClass.HasCentralCharacter d ω) : c = d := by
  induction ω using Quotient.inductionOn with
  | h π =>
    let := π.property.1
    let : Nontrivial π.obj :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.obj.representation.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : π.obj)
    ext z
    apply smul_left_injective ℂ hv
    exact (hc z v).symm.trans (hd z v)

set_option backward.isDefEq.respectTransparency false in
private theorem hasCentralCharacter_twist
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G))
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G))
    {c : Subgroup.center G →* ℂˣ} (hc : SmoothDualClass.HasCentralCharacter c ω) :
    SmoothDualClass.HasCentralCharacter
      ((χ.comp (Subgroup.center G).subtype) * c) (SmoothDualClass.twist χ hχ ω) := by
  induction ω using Quotient.inductionOn with
  | h π =>
    intro z v
    change (χ z : ℂ) • π.obj.representation z v =
      ((χ z : ℂ) * (c z : ℂ)) • v
    rw [hc z v, smul_smul]

section Central

variable [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)]
  (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]

private theorem exists_discreteSeriesCentralCharacter
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G))
    (hω : IsDiscreteSeriesClass A hA μ ω) :
    ∃ c : Subgroup.center G →* ℂˣ,
      SmoothDualClass.HasCentralCharacter c ω ∧ IsOpen (c.ker : Set (Subgroup.center G)) ∧
        ∀ z, ‖(c z : ℂ)‖ = 1 := by
  induction ω using Quotient.inductionOn with
  | h π =>
    obtain ⟨_, c, _⟩ := hω
    exact ⟨c.character, c.acts, c.isOpen_ker, c.norm_eq_one⟩

/-- The actual full-center scalar character of a discrete-series class. Its
existence comes from the existing square-integrability predicate. -/
def discreteSeriesCentralCharacter (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    Subgroup.center G →* ℂˣ :=
  Classical.choose (exists_discreteSeriesCentralCharacter A hA μ ω.val ω.property)

/-- The constructed character has the actual scalar action on the canonical class. -/
theorem discreteSeriesCentralCharacter_hasCentralCharacter
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    SmoothDualClass.HasCentralCharacter (discreteSeriesCentralCharacter A hA μ ω) ω.val :=
  (Classical.choose_spec (exists_discreteSeriesCentralCharacter A hA μ ω.val ω.property)).1

/-- This scalar character is independent of every choice of representative or witness. -/
theorem discreteSeriesCentralCharacter_eq_of_hasCentralCharacter
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) (c : Subgroup.center G →* ℂˣ)
    (hc : SmoothDualClass.HasCentralCharacter c ω.val) :
    discreteSeriesCentralCharacter A hA μ ω = c :=
  centralCharacter_unique ω.val
    (discreteSeriesCentralCharacter_hasCentralCharacter A hA μ ω) hc

/-- Evaluation on an actual representative recovers every supplied unitary character datum. -/
theorem discreteSeriesCentralCharacter_mk
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))
    (hπ : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ)
    (c : UnitaryCentralCharacter π.obj.representation) :
    discreteSeriesCentralCharacter A hA μ (discreteSeriesClass A hA μ π hπ) = c.character :=
  discreteSeriesCentralCharacter_eq_of_hasCentralCharacter A hA μ _ c.character c.acts

theorem isOpen_ker_discreteSeriesCentralCharacter
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    IsOpen ((discreteSeriesCentralCharacter A hA μ ω).ker : Set (Subgroup.center G)) :=
  (Classical.choose_spec (exists_discreteSeriesCentralCharacter A hA μ ω.val ω.property)).2.1

@[simp]
theorem norm_discreteSeriesCentralCharacter
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) (z : Subgroup.center G) :
    ‖(discreteSeriesCentralCharacter A hA μ ω z : ℂ)‖ = 1 :=
  (Classical.choose_spec (exists_discreteSeriesCentralCharacter A hA μ ω.val ω.property)).2.2 z

private def normOneCircleCharacter {H : Type uH} [Group H]
    (c : H →* ℂˣ) (hc : ∀ z, ‖(c z : ℂ)‖ = 1) : H →* Circle where
  toFun z := ⟨(c z : ℂ), by
    change (c z : ℂ) ∈ Metric.sphere 0 1
    exact mem_sphere_zero_iff_norm.mpr (hc z)⟩
  map_one' := by apply Circle.ext; simp
  map_mul' := by
    intro z w
    apply Circle.ext
    change (c (z * w) : ℂ) = (c z : ℂ) * (c w : ℂ)
    simp

/-- The same actual central scalar character, with values in the unit circle. -/
def discreteSeriesUnitaryCentralCharacter (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    Subgroup.center G →* Circle :=
  normOneCircleCharacter (discreteSeriesCentralCharacter A hA μ ω)
    (norm_discreteSeriesCentralCharacter A hA μ ω)

@[simp]
theorem discreteSeriesUnitaryCentralCharacter_coe
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) (z : Subgroup.center G) :
    (discreteSeriesUnitaryCentralCharacter A hA μ ω z : ℂ) =
      (discreteSeriesCentralCharacter A hA μ ω z : ℂ) := rfl

/-- The unit-circle scalar is the actual central action of each inducing representative. -/
theorem discreteSeriesUnitaryCentralCharacter_acts
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))
    (hπ : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation μ)
    (z : Subgroup.center G) (v : π.obj) :
    π.obj.representation z v =
      (discreteSeriesUnitaryCentralCharacter A hA μ (discreteSeriesClass A hA μ π hπ) z : ℂ) • v :=
  discreteSeriesCentralCharacter_hasCentralCharacter A hA μ
    (discreteSeriesClass A hA μ π hπ) z v

theorem continuous_discreteSeriesUnitaryCentralCharacter
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    Continuous (discreteSeriesUnitaryCentralCharacter A hA μ ω) := by
  exact (Units.continuous_val.comp
    (isLocallyConstant_of_isOpen_character_ker _
      (isOpen_ker_discreteSeriesCentralCharacter A hA μ ω)).continuous).subtype_mk _

/-- Restrict the actual class central character to any prescribed central subgroup. -/
def discreteSeriesCentralRestriction (B : Subgroup G) (hB : B ≤ Subgroup.center G)
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) : B →* Circle :=
  (discreteSeriesUnitaryCentralCharacter A hA μ ω).comp (Subgroup.inclusion hB)

theorem continuous_discreteSeriesCentralRestriction
    (B : Subgroup G) (hB : B ≤ Subgroup.center G)
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    Continuous (discreteSeriesCentralRestriction A hA μ B hB ω) :=
  (continuous_discreteSeriesUnitaryCentralCharacter A hA μ ω).comp
    (continuous_subtype_val.subtype_mk _)

end Central

section Twist

variable [NonarchimedeanGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)]
  (μ : MeasureTheory.Measure (G ⧸ A)) [MeasureTheory.Measure.IsHaarMeasure μ]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))

/-- The actual full-center character obeys the scalar twisting law. -/
theorem discreteSeriesCentralCharacter_unitaryTwist
    (χ : unitaryUnramifiedCharacters ν) (ω : DiscreteSeriesClass.{uG, uV} A hA μ) :
    discreteSeriesCentralCharacter A hA μ (χ • ω) =
      (χ.val.toMonoidHom.comp (Subgroup.center G).subtype) *
        discreteSeriesCentralCharacter A hA μ ω :=
  discreteSeriesCentralCharacter_eq_of_hasCentralCharacter A hA μ (χ • ω) _
    (hasCentralCharacter_twist ω.val χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν ⟨χ.val, χ.property.1⟩)
      (discreteSeriesCentralCharacter_hasCentralCharacter A hA μ ω))

omit [NonarchimedeanGroup G] in
/-- A unitary unramified character included in the unit circle at each actual point. -/
def unitaryUnramifiedCircleCharacter (χ : unitaryUnramifiedCharacters ν) : G →* Circle :=
  normOneCircleCharacter χ.val.toMonoidHom χ.property.2

omit [NonarchimedeanGroup G] in
@[simp]
theorem unitaryUnramifiedCircleCharacter_coe
    (χ : unitaryUnramifiedCharacters ν) (g : G) :
    (unitaryUnramifiedCircleCharacter ν χ g : ℂ) = (χ.val g : ℂ) := rfl

omit [NonarchimedeanGroup G] in
theorem continuous_unitaryUnramifiedCircleCharacter
    (χ : unitaryUnramifiedCharacters ν) :
    Continuous (unitaryUnramifiedCircleCharacter ν χ) :=
  (Units.continuous_val.comp χ.val.continuous).subtype_mk _

/-- Restriction to a central subgroup retains the actual twist law. -/
theorem discreteSeriesCentralRestriction_unitaryTwist
    (B : Subgroup G) (hB : B ≤ Subgroup.center G)
    (χ : unitaryUnramifiedCharacters ν) (ω : DiscreteSeriesClass.{uG, uV} A hA μ) (b : B) :
    discreteSeriesCentralRestriction A hA μ B hB (χ • ω) b =
      unitaryUnramifiedCircleCharacter ν χ b * discreteSeriesCentralRestriction A hA μ B hB ω b := by
  apply Circle.ext
  change (discreteSeriesCentralCharacter A hA μ (χ • ω) (Subgroup.inclusion hB b) : ℂ) =
    (χ.val b : ℂ) * (discreteSeriesCentralCharacter A hA μ ω (Subgroup.inclusion hB b) : ℂ)
  rw [discreteSeriesCentralCharacter_unitaryTwist]
  rfl

/-- The actual orbit map satisfies the central-character premise used by Fourier inversion. -/
theorem discreteSeriesCentralRestriction_orbitMap
    (B : Subgroup G) (hB : B ≤ Subgroup.center G)
    (ω : DiscreteSeriesClass.{uG, uV} A hA μ) (χ : unitaryUnramifiedCharacters ν) (b : B) :
    discreteSeriesCentralRestriction A hA μ B hB (discreteSeriesOrbitMap A hA μ ν ω χ).val b =
      unitaryUnramifiedCircleCharacter ν χ b * discreteSeriesCentralRestriction A hA μ B hB ω b :=
  discreteSeriesCentralRestriction_unitaryTwist A hA μ ν B hB χ ω b

end Twist

end Langlands.Plancherel

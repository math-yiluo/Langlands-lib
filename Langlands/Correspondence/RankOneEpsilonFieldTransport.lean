import Langlands.Correspondence.RankOneNormalizedEpsilon
import Langlands.LocalFactor.Abelian.SelfDualTransport

/-! # Rank-one arithmetic epsilon expressions on the original base field -/

noncomputable section

universe uF uP uV

namespace Langlands.Correspondence

open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance fieldEpsilonBottomAlgebra : Algebra (Padic p) (baseExtension F).field :=
  ((baseExtension F).asPadicField (p := p)).algebra

local instance fieldEpsilonBaseTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance fieldEpsilonBottomTopology : TopologicalSpace (baseExtension F).field :=
  (fieldData F (baseExtension F)).topology
local instance fieldEpsilonBaseMeasurable : MeasurableSpace F.Carrier := borel F.Carrier
local instance fieldEpsilonBottomMeasurable : MeasurableSpace (baseExtension F).field :=
  borel (baseExtension F).field
local instance fieldEpsilonBaseBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance fieldEpsilonBottomBorel : BorelSpace (baseExtension F).field := ⟨rfl⟩
local instance fieldEpsilonBaseTopologicalRing : IsTopologicalRing F.Carrier := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  infer_instance
local instance fieldEpsilonBottomTopologicalRing :
    IsTopologicalRing (baseExtension F).field := by
  let := (fieldData F (baseExtension F)).valuativeRel
  let := (fieldData F (baseExtension F)).localField
  infer_instance

private theorem continuous_baseFieldPadicEquiv : Continuous (baseFieldPadicEquiv F) := by
  let := ((baseExtension F).asPadicField (p := p)).canonicalNormedField
  let := F.canonicalNormedField
  exact (Weil.Local.extension_isometry ((baseExtension F).asPadicField (p := p)) F
    (baseFieldPadicEquiv F).toAlgHom).continuous

private theorem continuous_baseFieldPadicEquiv_symm :
    Continuous (baseFieldPadicEquiv F).symm := by
  let := ((baseExtension F).asPadicField (p := p)).canonicalNormedField
  let := F.canonicalNormedField
  exact (Weil.Local.extension_isometry F ((baseExtension F).asPadicField (p := p))
    (baseFieldPadicEquiv F).symm.toAlgHom).continuous

/-- Transport of actual nontrivial unitary additive characters to the bottom field. -/
def baseFieldAdditiveCharacterEquiv :
    NontrivialAdditiveCharacter F ≃ AdditiveCharacter F (baseExtension F) :=
  HarmonicAnalysis.FieldTransport.additiveCharacterEquiv
    (baseFieldPadicEquiv F).symm.toRingEquiv
    (continuous_baseFieldPadicEquiv_symm F) (continuous_baseFieldPadicEquiv F)

@[simp]
theorem baseFieldAdditiveCharacterEquiv_apply (ψ : NontrivialAdditiveCharacter F)
    (x : (baseExtension F).field) :
    baseFieldAdditiveCharacterEquiv F ψ x = ψ (baseFieldPadicEquiv F x) := rfl

/-- The original compatibility predicate specifies exactly this transported character. -/
theorem isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv
    (ψ : NontrivialAdditiveCharacter F) (ψ' : AdditiveCharacter F (baseExtension F)) :
    IsBaseCharacter F ψ ψ' ↔ ψ' = baseFieldAdditiveCharacterEquiv F ψ := by
  constructor
  · intro h
    exact HarmonicAnalysis.UnitaryAdditiveCharacter.ext h
  · rintro rfl
    intro x
    rfl

/-- Pushforward along the inverse bottom-field equivalence, with its actual inverse. -/
def baseFieldHaarMeasureEquiv :
    LocalAdditiveHaarMeasure F ≃ HaarMeasure F (baseExtension F) :=
  HarmonicAnalysis.FieldTransport.haarMeasureEquiv
    (baseFieldPadicEquiv F).symm.toRingEquiv
    (continuous_baseFieldPadicEquiv_symm F) (continuous_baseFieldPadicEquiv F)

@[simp]
theorem baseFieldHaarMeasureEquiv_measure (μ : LocalAdditiveHaarMeasure F) :
    (baseFieldHaarMeasureEquiv F μ).measure =
      MeasureTheory.Measure.map (baseFieldPadicEquiv F).symm μ.measure := rfl

/-- The intrinsic Fourier condition is preserved and reflected by these same maps. -/
theorem isSelfDual_baseFieldTransport_iff (ψ : NontrivialAdditiveCharacter F)
    (μ : LocalAdditiveHaarMeasure F) :
    CommonClosureSpectral.IsSelfDual F (baseExtension F)
      (baseFieldAdditiveCharacterEquiv F ψ) (baseFieldHaarMeasureEquiv F μ) ↔
        IsSelfDualMeasure F ψ μ :=
  PadicField.AbelianTransport.isSelfDual_iff F
    ((baseExtension F).asPadicField (p := p)) (baseFieldPadicEquiv F).symm ψ μ

/-- Every compatible bottom-field datum has the corresponding original-field
self-duality condition, using inverse transport of its actual Haar measure. -/
theorem isSelfDual_of_isBaseCharacter_iff
    (ψ : NontrivialAdditiveCharacter F) (ψ' : AdditiveCharacter F (baseExtension F))
    (hψ : IsBaseCharacter F ψ ψ') (μ : HaarMeasure F (baseExtension F)) :
    CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ ↔
      IsSelfDualMeasure F ψ ((baseFieldHaarMeasureEquiv F).symm μ) := by
  rw [(isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ ψ').1 hψ]
  simpa only [Equiv.apply_symm_apply] using
    isSelfDual_baseFieldTransport_iff F ψ ((baseFieldHaarMeasureEquiv F).symm μ)

/-- Existence is transported, without choosing or asserting a self-dual measure. -/
theorem baseSelfDualMeasureExists_iff (ψ : NontrivialAdditiveCharacter F) :
    (∃ (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F)),
      IsBaseCharacter F ψ ψ' ∧ CommonClosureSpectral.IsSelfDual F (baseExtension F) ψ' μ) ↔
      ∃ μ : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ μ := by
  constructor
  · rintro ⟨ψ', μ, hψ, hμ⟩
    exact ⟨(baseFieldHaarMeasureEquiv F).symm μ,
      (isSelfDual_of_isBaseCharacter_iff F ψ ψ' hψ μ).1 hμ⟩
  · rintro ⟨μ, hμ⟩
    exact ⟨baseFieldAdditiveCharacterEquiv F ψ, baseFieldHaarMeasureEquiv F μ,
      (isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ _).2 rfl,
      (isSelfDual_baseFieldTransport_iff F ψ μ).2 hμ⟩

/-- The full measure-dependent abelian expression agrees at corresponding data. -/
theorem abelianEpsilonExpression_baseFieldTransport (χ : QuasiCharacter F)
    (ψ : NontrivialAdditiveCharacter F) (μ : LocalAdditiveHaarMeasure F) :
    (fieldData F (baseExtension F)).abelianEpsilonExpression
      (baseFieldCharacterEquiv F χ) (baseFieldAdditiveCharacterEquiv F ψ)
      (baseFieldHaarMeasureEquiv F μ) =
        F.canonicalTopologicalData.abelianEpsilonExpression χ ψ μ :=
  PadicField.AbelianTransport.abelianEpsilonExpression_eq F
    ((baseExtension F).asPadicField (p := p)) (baseFieldPadicEquiv F).symm χ ψ μ

/-- The same comparison for every compatible bottom-field character and measure. -/
theorem abelianEpsilonExpression_of_isBaseCharacter (χ : QuasiCharacter F)
    (ψ : NontrivialAdditiveCharacter F) (ψ' : AdditiveCharacter F (baseExtension F))
    (hψ : IsBaseCharacter F ψ ψ') (μ : HaarMeasure F (baseExtension F)) :
    (fieldData F (baseExtension F)).abelianEpsilonExpression
      (baseFieldCharacterEquiv F χ) ψ' μ =
        F.canonicalTopologicalData.abelianEpsilonExpression χ ψ
          ((baseFieldHaarMeasureEquiv F).symm μ) := by
  rw [(isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ ψ').1 hψ]
  simpa only [Equiv.apply_symm_apply] using
    abelianEpsilonExpression_baseFieldTransport F χ ψ ((baseFieldHaarMeasureEquiv F).symm μ)

/-- Every actual continuous rank-one base restriction has the original-field
abelian epsilon expression, with its actual inverse-transported measure. -/
theorem conditionalPairEpsilonValue_on_baseField
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (χ η : QuasiCharacter F) (ψ : NontrivialAdditiveCharacter F)
    (ψ' : AdditiveCharacter F (baseExtension F)) (hψ : IsBaseCharacter F ψ ψ')
    (μ : HaarMeasure F (baseExtension F))
    {A B : Pair.{uF, uV} F (baseExtension F)}
    (hA : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ)) A)
    (hB : IsBaseRestriction F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) B)
    (hAc : A.toFiniteRepresentation.IsContinuous) (hBc : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ) :
    (CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
      A B hAc hBc Φ s : ℂ) =
      F.canonicalTopologicalData.abelianEpsilonExpression
        (F.canonicalTopologicalData.normalizedAbsPowerCharacter s * (χ * η)) ψ
        ((baseFieldHaarMeasureEquiv F).symm μ) := by
  rw [conditionalPairEpsilonValue_of_normalized_rankOneBaseRestriction
    F e eC h ε hε χ η ψ' μ hA hB hAc hBc Φ s,
    abelianEpsilonExpression_of_isBaseCharacter F _ ψ ψ' hψ μ]

/-- The complete arithmetic certificate expressed on the original field,
retaining existence and the universal identity for all self-dual measures. -/
theorem isArithmeticPairEpsilonFactor_rankOne_on_baseField_iff
    (e : ReciprocityCandidate F) (eC : ReciprocityFamily F)
    (h : IsBaseReciprocity F e eC)
    (ε : NonabelianSystem.Assignment.{uF, uV} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ : NontrivialAdditiveCharacter F) (χ η : QuasiCharacter F) (c : ℂˣ) (m : ℤ) :
    IsArithmeticPairEpsilonFactor F eC ε hε ψ
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ))
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) c m ↔
      (∃ μ : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ μ) ∧
      Nonempty (GeometricFrobenius F (baseExtension F)) ∧
      ∀ μ : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ μ → ∀ s : ℂ,
        F.canonicalTopologicalData.abelianEpsilonExpression
          (F.canonicalTopologicalData.normalizedAbsPowerCharacter s * (χ * η)) ψ μ =
          RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality c m s := by
  rw [isArithmeticPairEpsilonFactor_normalized_rankOneWeilCharacterClass_iff
    F e eC h ε hε ψ χ η c m]
  constructor
  · rintro ⟨hex, hΦ, hval⟩
    refine ⟨(baseSelfDualMeasureExists_iff F ψ).1 hex, hΦ, ?_⟩
    intro μ hμ s
    have hv := hval (baseFieldAdditiveCharacterEquiv F ψ) (baseFieldHaarMeasureEquiv F μ)
      ((isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv F ψ _).2 rfl)
      ((isSelfDual_baseFieldTransport_iff F ψ μ).2 hμ) s
    rwa [abelianEpsilonExpression_baseFieldTransport F _ ψ μ] at hv
  · rintro ⟨hex, hΦ, hval⟩
    refine ⟨(baseSelfDualMeasureExists_iff F ψ).2 hex, hΦ, ?_⟩
    intro ψ' μ hψ hμ s
    rw [abelianEpsilonExpression_of_isBaseCharacter F _ ψ ψ' hψ μ]
    exact hval ((baseFieldHaarMeasureEquiv F).symm μ)
      ((isSelfDual_of_isBaseCharacter_iff F ψ ψ' hψ μ).1 hμ) s

end Langlands.Correspondence

import Langlands.LocalFactor.NonabelianBrauerScaling
import Langlands.LocalFactor.NonabelianBrauerKernelStatement
import Langlands.LocalFactor.NonabelianDeterminantTransfer
import Langlands.LocalFactor.NonabelianRankOneScaling
import Langlands.LocalFactor.Inductive.GallagherDeterminantProof
import Langlands.LocalFactor.Abelian.Scaling
import Langlands.HarmonicAnalysis.PadicAdditiveCharacterSelfDuality

/-! # Determinants of Brauer relations and additive-character independence -/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The ratio of the two characters of a generator at the image of a unit of `E`. -/
def generatorCharacterRatio (E : Extension F) (g : Generator F E) (a : E.fieldˣ) : ℂˣ :=
  letI := (fieldData F g.extension).topology
  g.first (E.unitsInclusion g.extension g.inclusion a) /
    g.second (E.unitsInclusion g.extension g.inclusion a)

/-- Evaluation of the character ratios at one unit, written additively. -/
def characterRatioMap (E : Extension F) (a : E.fieldˣ) :
    Presentation F E →ₗ[ℤ] Additive ℂˣ :=
  Finsupp.linearCombination ℤ (fun g => Additive.ofMul (generatorCharacterRatio F E g a))

/-- The character-ratio evaluation is the determinant of the actual virtual class. -/
theorem characterRatioMap_eq_determinant (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (w : weilSubgroup F E)
    (z : Presentation F E) :
    characterRatioMap F E (reciprocityUnits F e E w) z =
      Additive.ofMul (ExactGrothendieckGroup.determinantCharacter (ContinuousPredicate F E)
        (virtualPresentation.{uF, uV} F e E z) w) := by
  induction z using Finsupp.induction_linear with
  | zero =>
    rw [map_zero, map_zero, ExactGrothendieckGroup.determinantCharacter_zero_apply]
    rfl
  | add x y hx hy =>
    rw [map_add, map_add, ExactGrothendieckGroup.determinantCharacter_add_apply, hx, hy]
    rfl
  | single g n =>
    rw [characterRatioMap, Finsupp.linearCombination_single]
    have hv : virtualPresentation.{uF, uV} F e E (Finsupp.single g n) =
        n • generatorClass F e E g := Finsupp.linearCombination_single _ _ _
    rw [hv, ExactGrothendieckGroup.determinantCharacter_zsmul_apply,
      determinant_generatorClass F e he E g w]
    rfl

/-- Every actual Brauer relation has trivial character-ratio product at every unit
of the base field. -/
theorem characterRatioMap_eq_zero (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (z : Presentation F E)
    (hz : presentationMap.{uF, uV} F e E z = 0) (a : E.fieldˣ) :
    characterRatioMap F E a z = 0 := by
  obtain ⟨w, rfl⟩ := exists_reciprocityUnits_eq F e E a
  rw [characterRatioMap_eq_determinant.{uF, uV} F e he E w z]
  have hz' : virtualPresentation.{uF, uV} F e E z = 0 := congrArg Subtype.val hz
  rw [hz', ExactGrothendieckGroup.determinantCharacter_zero_apply]
  rfl


end Langlands.LocalFactor.NonabelianBrauer

namespace Langlands.PadicField.TopologicalData

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- Every continuous unitary additive character is locally constant. -/
theorem isLocallyConstant_additiveCharacter
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    IsLocallyConstant ψ.complex := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨n, hn⟩ := T.exists_additiveTrivialAt ψ
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (T.additiveLattice n : Set F.Carrier),
    (T.isOpen_additiveLattice n).preimage (continuous_id.sub continuous_const),
    by simp [(T.additiveLattice n).zero_mem], fun y hy => ?_⟩
  have hy' : ψ (y - x) = 1 := hn _ hy
  have : y = (y - x) + x := by abel
  rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, this]
  change ((ψ.toAddChar ((y - x) + x) : Circle) : ℂ) = _
  rw [AddChar.map_add_eq_mul]
  change ((ψ (y - x) * ψ x : Circle) : ℂ) = _
  rw [hy', one_mul]

/-- Every nontrivial continuous unitary additive character is a scaling of a fixed one. -/
theorem exists_scale_eq
    (ψ ψ' : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∃ a : F.Carrierˣ, ψ' = ψ.scale a := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨a, ha⟩ := T.exists_eq_complex_mul_of_isLocallyConstant ψ ψ'.complex
    (T.isLocallyConstant_additiveCharacter ψ')
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply ψ'.nontrivial
    apply AddChar.ext
    intro x
    have hx := ha x
    rw [zero_mul, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
      HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply] at hx
    change ψ' x = 1
    apply Circle.ext
    rw [hx]
    rw [AddChar.map_zero_eq_one]
  refine ⟨Units.mk0 a ha0, ?_⟩
  ext x
  rw [HarmonicAnalysis.UnitaryAdditiveCharacter.scale_apply]
  have hx := ha x
  rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply] at hx
  exact hx

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Scaling the additive character adds the character-ratio evaluation. -/
theorem evaluationMap_scale_characterRatio (E : Extension F) (ψ : AdditiveCharacter F E)
    (measures : HaarFamily F) (a : E.fieldˣ) (z : Presentation F E) :
    letI := (fieldData F E).topology
    letI := (fieldData F E).valuativeRel
    letI := (fieldData F E).localField
    evaluationMap F E (ψ.scale a) measures z =
      characterRatioMap F E a z + evaluationMap F E ψ measures z := by
  let := (fieldData F E).topology
  let := (fieldData F E).valuativeRel
  let := (fieldData F E).localField
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    abel
  | single g n =>
    rw [evaluationMap_single, evaluationMap_single, characterRatioMap,
      Finsupp.linearCombination_single, generatorValue_scale, ofMul_mul]
    exact zsmul_add _ _ n

/-- The evaluation of an actual Brauer relation does not depend on the nontrivial
additive character. -/
theorem evaluationMap_additiveCharacter_independent (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (E : Extension F) (ψ ψ' : AdditiveCharacter F E)
    (measures : HaarFamily F) (z : Presentation F E)
    (hz : presentationMap.{uF, uV} F e E z = 0) :
    evaluationMap F E ψ' measures z = evaluationMap F E ψ measures z := by
  obtain ⟨a, rfl⟩ := (fieldData F E).exists_scale_eq ψ ψ'
  exact evaluationMap_scale_of_presentationMap_eq_zero.{uF, uV} F e he E ψ measures a z hz

end Langlands.LocalFactor.NonabelianBrauer

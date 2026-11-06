import Langlands.Global.GeneralLinearBlockIntrinsicMeasure
import Langlands.Automorphic.GeneralLinearConstantTermComparison

/-! # Intrinsic normalized block constant terms and the original matrix integrals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.GeneralLinearBlockUnipotent

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "H" => AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h)
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h)

local instance intrinsicConstantTermIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance intrinsicConstantTermSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance intrinsicConstantTermClosed :
    IsClosed (H : Set (AdelicGroupPoints F GLG)) :=
  GeneralLinearBlockUnipotent.isClosed_adelicPoints F h

local instance intrinsicConstantTermLocallyCompact : LocallyCompactSpace H :=
  (GeneralLinearBlockUnipotent.isClosed_adelicPoints F h).locallyCompactSpace

local instance intrinsicConstantTermQuotientBorelSpace : BorelSpace Q :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F GLG (subgroup F h)

private theorem integrable_borel_map_id (m : MeasurableSpace Q) (hm : m = borel Q)
    (mu : @Measure Q m) (phi : Q → ℂ) :
    (letI : MeasurableSpace Q := borel Q;
      Integrable phi (@Measure.map Q Q m (borel Q) id mu)) ↔
    (letI : MeasurableSpace Q := m;
      Integrable phi mu) := by
  subst m
  simp only [Measure.map_id]

private theorem constantTerm_borel_map_id (m : MeasurableSpace Q) (hm : m = borel Q)
    (mu : @Measure Q m) (f : ContinuousRationalFunctions F GLG)
    (g : AdelicGroupPoints F GLG) :
    (letI : MeasurableSpace Q := borel Q;
      constantTerm F GLG (subgroup F h) (@Measure.map Q Q m (borel Q) id mu) f g) =
    (letI : MeasurableSpace Q := m;
      constantTerm F GLG (subgroup F h) mu f g) := by
  subst m
  simp only [Measure.map_id]

variable [CompactSpace (AdeleQuotient F)]

local instance intrinsicConstantTermProbability :
    IsProbabilityMeasure
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) :=
  AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F GLG _

/-- Absolute integrability for the intrinsic normalization is exactly integrability
of the original matrix integrand. -/
theorem integrable_constantTermIntegrand_generalLinearBlock_intrinsic_iff
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    Integrable (constantTermIntegrand F GLG (subgroup F h) f g)
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) ↔
      Integrable (Langlands.Automorphic.constantTermIntegrand F n h
        (continuousGeneralLinearEquiv F n f)
        (GeneralLinearGroupPoints.adelicHomeomorph F n g)) (matrixQuotientHaar F a b) := by
  have hi := integrable_borel_map_id F h _
    (AdelicSubgroupPoints.rationalQuotientBorelSpace F GLG (subgroup F h)).measurable_eq
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h))
    (constantTermIntegrand F GLG (subgroup F h) f g)
  rw [normalizedRationalQuotientHaarMeasure_eq] at hi
  exact hi.symm.trans (integrable_constantTermIntegrand_generalLinearBlock_iff F h f g)

/-- The original matrix convergence theorem proves convergence for intrinsic subgroup Haar. -/
theorem hasConvergentConstantTerm_generalLinearBlock_intrinsic
    (f : ContinuousRationalFunctions F GLG) :
    HasConvergentConstantTerm F GLG (subgroup F h)
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) f := by
  intro g
  exact (integrable_constantTermIntegrand_generalLinearBlock_intrinsic_iff F h f g).mpr
    (Langlands.Automorphic.integrable_constantTermIntegrand h
      (continuousGeneralLinearEquiv F n f) (GeneralLinearGroupPoints.adelicHomeomorph F n g))

/-- The intrinsic normalized quotient integral equals the original matrix constant term. -/
theorem constantTerm_generalLinearBlock_intrinsic
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    constantTerm F GLG (subgroup F h)
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) f g =
      Langlands.Automorphic.constantTerm F n h (continuousGeneralLinearEquiv F n f)
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) := by
  have hc := constantTerm_borel_map_id F h _
    (AdelicSubgroupPoints.rationalQuotientBorelSpace F GLG (subgroup F h)).measurable_eq
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) f g
  rw [normalizedRationalQuotientHaarMeasure_eq] at hc
  exact hc.symm.trans (constantTerm_generalLinearBlock F h f g)

/-- The intrinsic normalized integral is complex linear on the full continuous space. -/
def intrinsicGeneralLinearBlockConstantTermLinearMap :
    ContinuousRationalFunctions F GLG →ₗ[ℂ] (AdelicGroupPoints F GLG → ℂ) :=
  compactConstantTermLinearMap F GLG (subgroup F h)
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h))

theorem intrinsicGeneralLinearBlockConstantTermLinearMap_apply
    (f : ContinuousRationalFunctions F GLG) (g : AdelicGroupPoints F GLG) :
    intrinsicGeneralLinearBlockConstantTermLinearMap F h f g =
      Langlands.Automorphic.constantTerm F n h (continuousGeneralLinearEquiv F n f)
        (GeneralLinearGroupPoints.adelicHomeomorph F n g) :=
  constantTerm_generalLinearBlock_intrinsic F h f g

/-- Positive ambient right translation intertwines the intrinsic integral operator. -/
theorem intrinsicGeneralLinearBlockConstantTermLinearMap_rightAction
    (f : ContinuousRationalFunctions F GLG) (x g : AdelicGroupPoints F GLG) :
    intrinsicGeneralLinearBlockConstantTermLinearMap F h (continuousRightAction F GLG x f) g =
      intrinsicGeneralLinearBlockConstantTermLinearMap F h f (g * x) :=
  constantTerm_rightAction F GLG (subgroup F h)
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) f x g

/-- Left multiplication of the argument by an actual block point preserves the integral. -/
theorem intrinsicGeneralLinearBlockConstantTermLinearMap_subgroup_mul
    (f : ContinuousRationalFunctions F GLG) (x : H) (g : AdelicGroupPoints F GLG) :
    intrinsicGeneralLinearBlockConstantTermLinearMap F h f (x.val * g) =
      intrinsicGeneralLinearBlockConstantTermLinearMap F h f g := by
  rw [intrinsicGeneralLinearBlockConstantTermLinearMap_apply,
    intrinsicGeneralLinearBlockConstantTermLinearMap_apply]
  exact (generalLinearBlockConstantTermLinearMap_apply F h f (x.val * g)).symm.trans
    ((generalLinearBlockConstantTermLinearMap_subgroup_mul F h f x g).trans
      (generalLinearBlockConstantTermLinearMap_apply F h f g))

/-- Intrinsic convergence and vanishing are equivalent to the original block vanishing law. -/
theorem hasVanishingConstantTerm_generalLinearBlock_intrinsic_iff
    (f : ContinuousRationalFunctions F GLG) :
    HasVanishingConstantTerm F GLG (subgroup F h)
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) f ↔
      ∀ g : AdelicGL F n, Langlands.Automorphic.constantTerm F n h
        (continuousGeneralLinearEquiv F n f) g = 0 := by
  constructor
  · intro hf g
    obtain ⟨g, rfl⟩ := (GeneralLinearGroupPoints.adelicHomeomorph F n).surjective g
    rw [← constantTerm_generalLinearBlock_intrinsic]
    exact hf.2 g
  · intro hf
    refine ⟨hasConvergentConstantTerm_generalLinearBlock_intrinsic F h f, ?_⟩
    intro g
    rw [constantTerm_generalLinearBlock_intrinsic]
    exact hf _

end Langlands.Automorphic.GroupSchemeFunctions

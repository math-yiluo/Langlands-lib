import Langlands.Global.GeneralLinearBlockUnipotentMeasure
import Langlands.Global.AdelicSubgroupHaarMeasure
import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Intrinsic normalized Haar for the actual two-block unipotent quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.GeneralLinearBlockUnipotent

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "H" => AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h)
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h)
local notation "M" => Matrix (Fin a) (Fin b) (AdeleQuotient F)

local instance intrinsicBlockIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance intrinsicBlockSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- Closedness is inherited from the represented actual block subgroup. -/
theorem isClosed_adelicPoints : IsClosed (H : Set (AdelicGroupPoints F GLG)) := by
  let j := GroupScheme.GeneralLinear.blockUnipotentHom (Fin n) (CommRingCat.of F)
    (Langlands.GeneralLinear.twoBlockWeight h)
  have hj := GroupScheme.GeneralLinear.isClosedSubgroup_blockUnipotentHom
    (Fin n) (CommRingCat.of F) (Langlands.GeneralLinear.twoBlockWeight h)
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffine
      (GroupScheme.GeneralLinear.blockUnipotentScheme (Fin n) (CommRingCat.of F)
        (Langlands.GeneralLinear.twoBlockWeight h)).X.left :=
    isAffine_of_isAffineHom j.hom.hom.left
  have hrange : Langlands.GroupScheme.SubgroupFunctor.range j = subgroup F h :=
    (GroupScheme.GeneralLinear.isRepresentedBy_blockUnipotent
      (Fin n) (CommRingCat.of F) (Langlands.GeneralLinear.twoBlockWeight h)).2
  rw [← hrange]
  exact AdelicSubgroupPoints.isClosed_adelicPoints_range F GLG j

local instance intrinsicBlockClosed : IsClosed (H : Set (AdelicGroupPoints F GLG)) :=
  isClosed_adelicPoints F h

local instance intrinsicBlockLocallyCompact : LocallyCompactSpace H :=
  (isClosed_adelicPoints F h).locallyCompactSpace

/-- The original block coordinate group law proves actual subgroup commutativity. -/
theorem adelicPoints_mul_comm (x y : H) : x * y = y * x := by
  apply (adelicCoordinates F h).injective
  rw [map_mul, map_mul, mul_comm]

local instance intrinsicBlockHaarRightInvariant :
    (Measure.haar : Measure H).IsMulRightInvariant where
  map_mul_right_eq_self x := by
    have heq : (fun y : H => y * x) = (fun y : H => x * y) :=
      funext fun y => adelicPoints_mul_comm F h y x
    rw [heq, map_mul_left_eq_self]

local instance intrinsicBlockQuotientBorelSpace : BorelSpace Q :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F GLG (subgroup F h)
local instance intrinsicBlockMatrixMeasurableSpace : MeasurableSpace M := borel M
local instance intrinsicBlockMatrixBorelSpace : BorelSpace M := ⟨rfl⟩

variable [CompactSpace (AdeleQuotient F)]

/-- The existing intrinsic subgroup Haar scaled by the actual quotient mass. -/
def normalizedBlockHaarMeasure : Measure H :=
  AdelicSubgroupPoints.normalizedHaarMeasure F GLG (subgroup F h)

/-- The intrinsic normalized quotient maps to the original matrix Haar probability. -/
theorem map_quotientHomeomorph_normalizedRationalQuotientHaarMeasure :
    Measure.map (quotientHomeomorph F h)
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) =
        matrixQuotientHaar F a b := by
  let mu := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)
  let nu : Measure M := Measure.map (quotientHomeomorph F h) mu
  let : IsProbabilityMeasure mu :=
    AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F GLG _
  let : IsProbabilityMeasure nu := by dsimp [nu]; infer_instance
  let : nu.IsAddLeftInvariant := by
    constructor
    intro X
    let x : H := (adelicCoordinates F h).symm (Multiplicative.ofAdd (matrixLift X))
    have hx : matrixQuotientMap (adelicCoordinates F h x).toAdd = X := by
      dsimp [x]
      rw [(adelicCoordinates F h).apply_symm_apply]
      exact matrixQuotientMap_matrixLift X
    have heq : (fun Y : M => X + Y) ∘ quotientHomeomorph F h =
        quotientHomeomorph F h ∘ LeftCosetSpace.rightTranslate
          (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h)) x := by
      funext q
      rw [Function.comp_apply, Function.comp_apply, quotientHomeomorph_rightTranslate, hx,
        add_comm]
    change Measure.map (fun Y : M => X + Y) (Measure.map (quotientHomeomorph F h) mu) = nu
    rw [Measure.map_map (by fun_prop) (quotientHomeomorph F h).measurable, heq,
      ← Measure.map_map (quotientHomeomorph F h).measurable
        (LeftCosetSpace.continuous_rightTranslate _ x).measurable]
    rw [(AdelicSubgroupPoints.measurePreserving_rightTranslate_normalizedRationalQuotientHaarMeasure
      F GLG (subgroup F h) x).map_eq]
  let : (matrixQuotientHaar F a b).IsAddHaarMeasure :=
    matrixQuotientHaar_isAddHaarMeasure F a b
  have heq : nu = (Measure.addHaarScalarFactor nu (matrixQuotientHaar F a b) : ℝ≥0∞) •
      matrixQuotientHaar F a b := by
    simpa only [ENNReal.smul_def] using
      Measure.isAddInvariant_eq_smul_of_compactSpace nu (matrixQuotientHaar F a b)
  have hc := congrArg (fun m : Measure M => m Set.univ) heq
  simp only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one] at hc
  rw [← hc, one_smul] at heq
  exact heq

/-- The identity from the inherited quotient sigma-algebra to its Borel sigma-algebra
identifies the intrinsic measure with the original measure. -/
theorem normalizedRationalQuotientHaarMeasure_eq :
    @Measure.map Q Q _ (borel Q) id
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F GLG (subgroup F h)) =
      rationalQuotientMeasure F h := by
  have hid : @Measurable Q Q _ (borel Q) id :=
    measurable_id.mono le_rfl (le_of_eq BorelSpace.measurable_eq.symm)
  let : MeasurableSpace Q := borel Q
  let : BorelSpace Q := ⟨rfl⟩
  apply (quotientHomeomorph F h).toMeasurableEquiv.map_measurableEquiv_injective
  exact (Measure.map_map (quotientHomeomorph F h).measurable hid).trans
    ((map_quotientHomeomorph_normalizedRationalQuotientHaarMeasure F h).trans
      (map_quotientHomeomorph_rationalQuotientMeasure F h).symm)

omit [CompactSpace (AdeleQuotient F)] in
private theorem compatible_borel_map_id (m : MeasurableSpace Q) (hm : m = borel Q)
    (hb : @BorelSpace Q _ m) (nu : @Measure Q m)
    (hc : letI : MeasurableSpace Q := m
          letI : BorelSpace Q := hb
          Langlands.QuotientIntegration.IsCompatible
            (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))
            (normalizedBlockHaarMeasure F h) Measure.count nu) :
    letI : MeasurableSpace Q := borel Q
    letI : BorelSpace Q := ⟨rfl⟩
    Langlands.QuotientIntegration.IsCompatible
      (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))
      (normalizedBlockHaarMeasure F h) Measure.count
      (@Measure.map Q Q m (borel Q) id nu) := by
  subst m
  simpa only [Measure.map_id] using hc

section Borel

local instance originalBlockQuotientMeasurableSpace : MeasurableSpace Q := borel Q
local instance originalBlockQuotientBorelSpace : BorelSpace Q := ⟨rfl⟩

/-- The original quotient measure satisfies the counting-measure Weil formula with the
simultaneously normalized intrinsic subgroup Haar. -/
theorem rationalQuotientMeasure_isCompatible :
    Langlands.QuotientIntegration.IsCompatible
      (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h))
      (normalizedBlockHaarMeasure F h) Measure.count (rationalQuotientMeasure F h) := by
  have hc := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isCompatible
    F GLG (subgroup F h)
  have hm := (AdelicSubgroupPoints.rationalQuotientBorelSpace F GLG
    (subgroup F h)).measurable_eq
  have ht := compatible_borel_map_id F h _ hm
    (AdelicSubgroupPoints.rationalQuotientBorelSpace F GLG (subgroup F h)) _ hc
  rw [normalizedRationalQuotientHaarMeasure_eq] at ht
  exact ht

end Borel

end Langlands.Global.GeneralLinearBlockUnipotent

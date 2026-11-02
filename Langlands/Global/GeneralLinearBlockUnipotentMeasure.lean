import Langlands.Global.GeneralLinearBlockUnipotentQuotient

/-! # The original normalized measure on the actual two-block rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Global.GeneralLinearBlockUnipotent

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ} (h : a + b = n)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F GLG (subgroup F h)
local notation "M" => Matrix (Fin a) (Fin b) (AdeleQuotient F)

local instance quotientMeasurableSpace : MeasurableSpace Q := borel Q
local instance quotientBorelSpace : BorelSpace Q := ⟨rfl⟩
local instance matrixMeasurableSpace : MeasurableSpace M := borel M
local instance matrixBorelSpace : BorelSpace M := ⟨rfl⟩

variable [CompactSpace (AdeleQuotient F)]

/-- Transport the original normalized matrix Haar measure to the actual quotient,
using its Borel sigma algebra explicitly. -/
def rationalQuotientMeasure : @Measure Q (borel Q) :=
  Measure.map (quotientHomeomorph F h).symm (matrixQuotientHaar F a b)

instance rationalQuotientMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (rationalQuotientMeasure F h) := by
  unfold rationalQuotientMeasure
  infer_instance

theorem rationalQuotientMeasure_univ :
    rationalQuotientMeasure F h Set.univ = 1 :=
  measure_univ

/-- The forward comparison returns exactly the original measure, including its normalization. -/
theorem map_quotientHomeomorph_rationalQuotientMeasure :
    Measure.map (quotientHomeomorph F h) (rationalQuotientMeasure F h) =
      matrixQuotientHaar F a b :=
  (quotientHomeomorph F h).toMeasurableEquiv.map_map_symm

theorem measurePreserving_quotientHomeomorph :
    MeasurePreserving (quotientHomeomorph F h) (rationalQuotientMeasure F h)
      (matrixQuotientHaar F a b) :=
  ⟨(quotientHomeomorph F h).measurable,
    map_quotientHomeomorph_rationalQuotientMeasure F h⟩

theorem measurePreserving_quotientHomeomorph_symm :
    MeasurePreserving (quotientHomeomorph F h).symm (matrixQuotientHaar F a b)
      (rationalQuotientMeasure F h) :=
  ⟨(quotientHomeomorph F h).symm.measurable, rfl⟩

/-- Positive right translation on the actual subgroup quotient preserves the transported
normalized measure. -/
theorem measurePreserving_rightTranslate
    (x : AdelicSubgroupPoints.adelicPoints F GLG (subgroup F h)) :
    MeasurePreserving
      (LeftCosetSpace.rightTranslate
        (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h)) x)
      (rationalQuotientMeasure F h) (rationalQuotientMeasure F h) := by
  have := matrixQuotientHaar_isAddHaarMeasure F a b
  have heq :
      LeftCosetSpace.rightTranslate
          (AdelicSubgroupPoints.rationalSubgroup F GLG (subgroup F h)) x =
        (quotientHomeomorph F h).symm ∘
          (fun X : M => X + matrixQuotientMap (adelicCoordinates F h x).toAdd) ∘
            quotientHomeomorph F h := by
    funext q
    apply (quotientHomeomorph F h).injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply,
      quotientHomeomorph_rightTranslate]
  rw [heq]
  exact (measurePreserving_quotientHomeomorph_symm F h).comp
    ((measurePreserving_add_right (matrixQuotientHaar F a b)
      (matrixQuotientMap (adelicCoordinates F h x).toAdd)).comp
        (measurePreserving_quotientHomeomorph F h))

end Langlands.Global.GeneralLinearBlockUnipotent

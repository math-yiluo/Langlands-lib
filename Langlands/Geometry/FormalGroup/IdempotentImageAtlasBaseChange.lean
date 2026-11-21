import Langlands.Geometry.FormalGroup.FormalIdempotentImageAtlas
import Langlands.Geometry.FormalGroup.AtlasBaseChange
import Langlands.Geometry.FormalGroup.CoefficientCoherence

/-! # Coefficient extension of formal projector-image atlases -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {e : ModuleLaw.Hom M M}
variable (I : IdempotentImageCover e τ) (S : CommAlgCat.{v} R)

private theorem baseCoefficient_square (b : I.atlas.baseOpens S) :
    (I.atlas.baseChartCoefficient S b).comp
      (IsScalarTower.toAlgHom O R (Localization.Away (I.atlas.baseSource S b).val)) =
    (IsScalarTower.toAlgHom O S (Localization.Away b.val)).comp (IsScalarTower.toAlgHom O R S) := by
  apply AlgHom.ext
  intro r
  change I.atlas.baseChartCoefficient S b (algebraMap R (Localization.Away (I.atlas.baseSource S b).val) r) =
    algebraMap S (Localization.Away b.val) (algebraMap R S r)
  rw [I.atlas.baseChartCoefficient_algebraMap, IsScalarTower.algebraMap_apply R S]

private def baseImage (b : I.atlas.baseOpens S) :
    ModuleLaw.Hom.IdempotentImage ((e.map (IsScalarTower.toAlgHom O R S)).map
      (IsScalarTower.toAlgHom O S (Localization.Away b.val))) (I.atlas.baseChart S b) :=
  let a := I.atlas.baseSource S b
  let α := IsScalarTower.toAlgHom O R (Localization.Away a.val)
  let β := I.atlas.baseChartCoefficient S b
  let γ := IsScalarTower.toAlgHom O R S
  let δ := IsScalarTower.toAlgHom O S (Localization.Away b.val)
  ((I.image a).2.map β).transport (mapSquareIso M α β γ δ (I.baseCoefficient_square S b))
    (mapSquareIso_natural e α β γ δ (I.baseCoefficient_square S b)).symm

/-- Extend the genuine image retractions on the chosen preimages of the new
principal generators. -/
def baseChange : IdempotentImageCover (e.map (IsScalarTower.toAlgHom O R S)) τ where
  opens := I.atlas.baseOpens S
  covers := I.atlas.baseOpens_covers S
  image b := ⟨I.atlas.baseChart S b, I.baseImage S b⟩

/-- The extended image inclusion has the original inclusion's extended coordinates. -/
theorem baseChange_image_inclusion_coordinates (b : I.atlas.baseOpens S) :
    ((I.baseChange S).image b).2.inclusion.toHom.toCoordinateMap =
      (I.image (I.atlas.baseSource S b)).2.inclusion.toHom.toCoordinateMap.map
        (I.atlas.baseChartCoefficient S b).toRingHom :=
  CoordinateMap.id_comp _

/-- The extended image projection has the original projection's extended coordinates. -/
theorem baseChange_image_projection_coordinates (b : I.atlas.baseOpens S) :
    ((I.baseChange S).image b).2.projection.toHom.toCoordinateMap =
      (I.image (I.atlas.baseSource S b)).2.projection.toHom.toCoordinateMap.map
        (I.atlas.baseChartCoefficient S b).toRingHom :=
  CoordinateMap.comp_id _

/-- Both coefficient-extension routes give the same transition coordinate maps. -/
theorem baseChange_transition_coordinates (B : CommAlgCat.{v} S) (a b : I.atlas.baseOpens S)
    (ha : IsUnit (algebraMap S B a.val)) (hb : IsUnit (algebraMap S B b.val)) :
    ((I.baseChange S).atlas.transition B a b ha hb).hom.toHom.toCoordinateMap =
      ((I.atlas.baseChange S).transition B a b ha hb).hom.toHom.toCoordinateMap := by
  let B' := BasicAtlas.restrictTest S B
  let a' := I.atlas.baseSource S a
  let b' := I.atlas.baseSource S b
  let ha' := I.atlas.baseSource_unit S B a ha
  let hb' := I.atlas.baseSource_unit S B b hb
  let P := ((I.baseChange S).image a).2.overChartTest B ha
  let Q := ((I.baseChange S).image b).2.overChartTest B hb
  let P' := (I.image a').2.overChartTest B' ha'
  let Q' := (I.image b').2.overChartTest B' hb'
  rw [show (I.atlas.baseChange S).transition B a b ha hb = I.atlas.baseTransition S B a b ha hb from rfl,
    BasicAtlas.baseTransition_coordinates]
  change (P.iso Q).hom.toHom.toCoordinateMap = (P'.iso Q').hom.toHom.toCoordinateMap
  simp only [ModuleLaw.Hom.IdempotentImage.iso_hom, ModuleLaw.Hom.comp_toHom,
    CommLaw.Hom.comp_toCoordinateMap]
  dsimp only [P, Q, P', Q']
  simp only [ModuleLaw.Hom.IdempotentImage.overChartTest_inclusion_coordinates,
    ModuleLaw.Hom.IdempotentImage.overChartTest_projection_coordinates,
    baseChange_image_inclusion_coordinates, baseChange_image_projection_coordinates,
    CoordinateMap.map_ringHom_comp]
  rw [I.atlas.baseCoefficient_comp S B b hb, I.atlas.baseCoefficient_comp S B a ha]

/-- The extended retractions give exactly the coefficient extension of the image atlas. -/
theorem baseChange_atlas : (I.baseChange S).atlas = I.atlas.baseChange S := by
  have ht : (I.baseChange S).atlas.transition = (I.atlas.baseChange S).transition := by
    funext B a b ha hb
    apply Iso.ext_hom
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    exact I.baseChange_transition_coordinates S B a b ha hb
  unfold IdempotentImageCover.atlas BasicAtlas.baseChange at ht ⊢
  congr 1

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

import Langlands.Geometry.FormalGroup.DivisionImageOrderAtlas

/-! # The atlas induced by a global presentation of a projector image -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {e : ModuleLaw.Hom M M} (P : ModuleLaw.Hom.IdempotentImage e N)
variable (s : Set R) (hs : Ideal.span s = ⊤)

/-- Restrict a genuine global formal projector retraction on a given principal cover. -/
def ofGlobalImageCover : IdempotentImageCover e τ where
  opens := s
  covers := hs
  image b := ⟨N.map (IsScalarTower.toAlgHom O R (Localization.Away b.val)),
    P.map (IsScalarTower.toAlgHom O R (Localization.Away b.val))⟩

/-- On a test, these image transitions have the coordinates of the identity. -/
theorem ofGlobalImageCover_transition_coordinates (B : CommAlgCat.{v} R) (a b : s)
    (ha : IsUnit (algebraMap R B a.val)) (hb : IsUnit (algebraMap R B b.val)) :
    ((ofGlobalImageCover P s hs).atlas.transition B a b ha hb).hom.toHom.toCoordinateMap =
      CoordinateMap.id := by
  let α := IsScalarTower.toAlgHom O R (Localization.Away a.val)
  let β := IsScalarTower.toAlgHom O R (Localization.Away b.val)
  let P₁ := (P.map α).overChartTest B ha
  let P₂ := (P.map β).overChartTest B hb
  change (P₁.iso P₂).hom.toHom.toCoordinateMap = _
  rw [ModuleLaw.Hom.IdempotentImage.iso_hom]
  simp only [ModuleLaw.Hom.comp_toHom, CommLaw.Hom.comp_toCoordinateMap]
  dsimp only [P₁, P₂]
  rw [ModuleLaw.Hom.IdempotentImage.overChartTest_projection_coordinates,
    ModuleLaw.Hom.IdempotentImage.overChartTest_inclusion_coordinates]
  change ((P.projection.toHom.toCoordinateMap.map (algebraMap R (Localization.Away b.val))).map
    (coefficientLift (O := O) b.val B hb).toRingHom).comp
    ((P.inclusion.toHom.toCoordinateMap.map (algebraMap R (Localization.Away a.val))).map
      (coefficientLift (O := O) a.val B ha).toRingHom) = _
  rw [CoordinateMap.map_ringHom_comp, CoordinateMap.map_ringHom_comp,
    globalCoefficient_comp, globalCoefficient_comp, ← CoordinateMap.map_comp]
  change (P.projection.comp P.inclusion).toHom.toCoordinateMap.map (algebraMap R B) = _
  rw [P.projection_inclusion]
  exact CoordinateMap.map_id _

/-- The atlas of the restricted global image equals the global-law cover atlas. -/
theorem ofGlobalImageCover_atlas : (ofGlobalImageCover P s hs).atlas = BasicAtlas.ofGlobalCover N s hs := by
  have h : (ofGlobalImageCover P s hs).atlas.transition = (BasicAtlas.ofGlobalCover N s hs).transition := by
    funext B a b ha hb
    apply Iso.ext_hom
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    refine (ofGlobalImageCover_transition_coordinates P s hs B a b ha hb).trans ?_
    exact (CoordinateMap.id_comp (CoordinateMap.id : CoordinateMap B τ τ)).symm
  unfold IdempotentImageCover.atlas BasicAtlas.ofGlobalCover at h ⊢
  congr 1

variable {D : Type w} [Ring D] [Algebra O D]
variable {E : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) M} (I : E.DivisionImage N)

/-- The order coordinate series on the global image cover are the extended global image action. -/
theorem ofGlobalImageCover_divisionOrder_action (b : s) (d : D) :
    ((((ofGlobalImageCover I s hs).divisionOrder E).chart b).action d).toHom.toCoordinateMap =
      ((I.order.map (IsScalarTower.toAlgHom O R (Localization.Away b.val))).action d).toHom.toCoordinateMap := by
  change ((I.projection.toHom.toCoordinateMap.map (algebraMap R (Localization.Away b.val))).comp
    (((E.action (0, d)).toHom.toCoordinateMap.map (algebraMap R (Localization.Away b.val))).comp
      (I.inclusion.toHom.toCoordinateMap.map (algebraMap R (Localization.Away b.val))))) =
    (I.projection.toHom.toCoordinateMap.comp
      ((E.action (0, d)).toHom.toCoordinateMap.comp I.inclusion.toHom.toCoordinateMap)).map
        (algebraMap R (Localization.Away b.val))
  rw [CoordinateMap.map_comp, CoordinateMap.map_comp]

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

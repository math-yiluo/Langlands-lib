import Langlands.Geometry.FormalGroup.AtlasOrderCoordinateIso
import Langlands.Geometry.FormalGroup.IdempotentImageAtlasBaseChange
import Langlands.Geometry.FormalGroup.GlobalIdempotentImageAtlas
import Langlands.Geometry.FormalGroup.OrderActionCentralAtlas
import Langlands.Geometry.FormalGroup.SpecialAtlasBaseChange
import Langlands.Geometry.FormalGroup.SplitDivisionCentralScalars

/-! # Central division-image atlases under coefficient extension and global restriction -/

noncomputable section

universe u v w c

namespace Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

open CategoryTheory BasicAtlas

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {C : Type c} [CommRing C] [Algebra C D] [Algebra C R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {E : ModuleLaw.OrderAction (Dᵐᵒᵖ × D) M}
variable (I : IdempotentImageCover E.divisionProjector τ)

/-- The structural central tangent condition on the split order passes to every image chart. -/
theorem divisionOrder_centralTangent
    (hs : E.HasStructuralDivisionTangent (algebraMap C D) (algebraMap C R))
    (b : I.atlas.opens) (a : C) (x : τ → Localization.Away b.val) :
    ((I.divisionOrder E).chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
      algebraMap C (Localization.Away b.val) a • x := by
  let φ := IsScalarTower.toAlgHom O R (Localization.Away b.val)
  have hs' : (E.map φ).HasStructuralDivisionTangent
      (algebraMap C D) (algebraMap C (Localization.Away b.val)) := by
    rw [IsScalarTower.algebraMap_eq C R (Localization.Away b.val)]
    exact hs.map φ
  exact ModuleLaw.OrderAction.DivisionImage.structuralCentralTangent (E := E.map φ)
    (I.image b).2 hs' a x

section BaseChange

variable (S : CommAlgCat.{v} R)

private theorem baseChange_divisionOrder_chart_coordinates (b : I.atlas.baseOpens S) (d : D) :
    ((((I.baseChange S).divisionOrder (E.map (IsScalarTower.toAlgHom O R S))).chart b).action d).toHom.toCoordinateMap =
      (((I.divisionOrder E).baseOrderChart S b).action d).toHom.toCoordinateMap := by
  let a := I.atlas.baseSource S b
  let a₀ := (I.image a).2
  let b₀ := ((I.baseChange S).image b).2
  let β := (I.atlas.baseChartCoefficient S b).toRingHom
  change b₀.projection.toHom.toCoordinateMap.comp
      ((((E.action (0, d)).toHom.toCoordinateMap.map (algebraMap R S)).map
        (algebraMap S (Localization.Away b.val))).comp b₀.inclusion.toHom.toCoordinateMap) =
    (a₀.projection.toHom.toCoordinateMap.comp
      (((E.action (0, d)).toHom.toCoordinateMap.map (algebraMap R (Localization.Away a.val))).comp
        a₀.inclusion.toHom.toCoordinateMap)).map β
  dsimp only [b₀]
  rw [I.baseChange_image_inclusion_coordinates S b, I.baseChange_image_projection_coordinates S b,
    CoordinateMap.map_comp, CoordinateMap.map_comp, CoordinateMap.map_ringHom_comp,
    CoordinateMap.map_ringHom_comp]
  have h : (algebraMap S (Localization.Away b.val)).comp (algebraMap R S) =
      β.comp (algebraMap R (Localization.Away a.val)) := by
    ext r
    change algebraMap S (Localization.Away b.val) (algebraMap R S r) =
      I.atlas.baseChartCoefficient S b (algebraMap R (Localization.Away a.val) r)
    rw [I.atlas.baseChartCoefficient_algebraMap,
      IsScalarTower.algebraMap_apply R S (Localization.Away b.val)]
  rw [h]

variable (hs : ∀ (b : I.atlas.opens) (a : C) (x : τ → Localization.Away b.val),
  ((I.divisionOrder E).chart b).fiberTangent (RingHom.id _) (algebraMap C D a) x =
    algebraMap C (Localization.Away b.val) a • x)
variable (ht : ∀ (b : (I.baseChange S).atlas.opens) (a : C) (x : τ → Localization.Away b.val),
  (((I.baseChange S).divisionOrder (E.map (IsScalarTower.toAlgHom O R S))).chart b).fiberTangent
    (RingHom.id _) (algebraMap C D a) x = algebraMap C (Localization.Away b.val) a • x)

/-- Central change of scalars on an extended image atlas agrees with extending the
original central atlas, by actual identity-coordinate order isomorphisms. -/
def baseChangeCentralIso : BasicAtlas.OrderAction.Iso
    (((I.baseChange S).divisionOrder (E.map (IsScalarTower.toAlgHom O R S))).centralAtlasOrder ht)
    (((I.divisionOrder E).centralAtlasOrder hs).baseChange S) rfl := by
  let left := ((I.baseChange S).divisionOrder (E.map (IsScalarTower.toAlgHom O R S))).centralAtlasOrder ht
  let right := ((I.divisionOrder E).centralAtlasOrder hs).baseChange S
  refine BasicAtlas.OrderAction.Iso.ofIdenticalChartCoordinates left right rfl ?_ ?_ ?_
  · intro B b hb
    rfl
  · intro B b hb d
    have h := I.baseChange_divisionOrder_chart_coordinates S b d
    have hc := congrArg (fun q : CoordinateMap (Localization.Away b.val) τ τ =>
      q.map (coefficientLift (O := C) b.val B hb).toRingHom) h
    exact hc
  · intro B b c hb hc
    let X := (I.divisionOrder E).centralAtlas hs
    have h := I.baseChange_transition_coordinates S B b c hb hc
    have h₁ := I.atlas.baseTransition_coordinates S B b c hb hc
    have h₂ := X.baseTransition_coordinates S B b c hb hc
    exact h.trans (h₁.trans h₂.symm)

end BaseChange

section GlobalCover

variable (P : E.DivisionImage N) (hs : E.HasStructuralDivisionTangent (algebraMap C D) (algebraMap C R))
variable (s : Set R) (hcover : Ideal.span s = ⊤)

/-- The centralized atlas of a global retraction compares to the cover atlas of its
actual central formal module and division order. -/
def globalImageCentralIso : BasicAtlas.OrderAction.Iso
    (((ofGlobalImageCover P s hcover).divisionOrder E).centralAtlasOrder
      ((ofGlobalImageCover P s hcover).divisionOrder_centralTangent hs))
    (BasicAtlas.ofGlobalCoverOrderAction (P.centralOrder hs) s hcover) rfl := by
  let I := ofGlobalImageCover P s hcover
  let left := (I.divisionOrder E).centralAtlasOrder (I.divisionOrder_centralTangent hs)
  let right := BasicAtlas.ofGlobalCoverOrderAction (P.centralOrder hs) s hcover
  refine BasicAtlas.OrderAction.Iso.ofIdenticalChartCoordinates left right rfl ?_ ?_ ?_
  · intro B b hb
    rfl
  · intro B b hb d
    have h := ofGlobalImageCover_divisionOrder_action s hcover P b d
    have hc := congrArg (fun q : CoordinateMap (Localization.Away b.val) τ τ =>
      q.map (coefficientLift (O := C) b.val B hb).toRingHom) h
    exact hc
  · intro B b c hb hc
    have h := ofGlobalImageCover_transition_coordinates P s hcover B b c hb hc
    exact h.trans (CoordinateMap.id_comp (CoordinateMap.id : CoordinateMap B τ τ)).symm

end GlobalCover

end Langlands.FormalGroup.ModuleLaw.IdempotentImageCover

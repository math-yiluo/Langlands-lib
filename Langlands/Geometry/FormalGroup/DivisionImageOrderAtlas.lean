import Langlands.Geometry.FormalGroup.FormalIdempotentImageAtlas
import Langlands.Geometry.FormalGroup.GlobalAtlasOrderAction
import Langlands.Geometry.FormalGroup.OrderIso
import Langlands.Geometry.FormalGroup.SplitOrderFormalSummand

/-! # The division order action on an atlas of the division projector image -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {B : Type w} [Ring B] [Algebra O B]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {P : ModuleLaw O R υ}
variable {E : OrderAction (Bᵐᵒᵖ × B) M}

namespace OrderAction.DivisionImage

/-- The actual comparison between two division image charts commutes with the order. -/
def orderIso (I : E.DivisionImage N) (J : E.DivisionImage P) :
    OrderAction.Iso I.order J.order :=
  OrderAction.Iso.ofModuleIso (I.iso J) (by
    intro b
    let f := E.action (0, b)
    change (I.restrictHom J (ModuleLaw.Hom.id M)).comp (I.restrictHom I f) =
      (J.restrictHom J f).comp (I.restrictHom J (ModuleLaw.Hom.id M))
    rw [← I.restrictHom_comp I J (ModuleLaw.Hom.id M) f (by simp [f]),
      ← I.restrictHom_comp J J f (ModuleLaw.Hom.id M) (by simp),
      ModuleLaw.Hom.id_comp, ModuleLaw.Hom.comp_id])

variable {a : R} {N' : ModuleLaw O (Localization.Away a) τ}
variable (I : (E.map (IsScalarTower.toAlgHom O R (Localization.Away a))).DivisionImage N')
variable (A : CommAlgCat.{v} R) (ha : IsUnit (algebraMap R A a))

set_option backward.isDefEq.respectTransparency false in
/-- The division order on the chart extends to the order on its test-algebra image. -/
theorem overChartTest_order_action (b : B) :
    (I.order.map (BasicAtlas.coefficientLift (O := O) a A ha)).action b =
      (order (E := E.map (IsScalarTower.toAlgHom O R A)) (I.overChartTest A ha)).action b := by
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  let f := BasicAtlas.coefficientLift (O := O) a A ha
  change (I.projection.toHom.toCoordinateMap.comp
    ((((E.map (IsScalarTower.toAlgHom O R (Localization.Away a))).action (0, b)).toHom.toCoordinateMap).comp
      I.inclusion.toHom.toCoordinateMap)).map f.toRingHom =
    (I.overChartTest A ha).projection.toHom.toCoordinateMap.comp
      (((E.map (IsScalarTower.toAlgHom O R A)).action (0, b)).toHom.toCoordinateMap.comp
        (I.overChartTest A ha).inclusion.toHom.toCoordinateMap)
  have hm := BasicAtlas.globalOrderChart_coordinates E a A ha (0, b)
  change (((E.map (IsScalarTower.toAlgHom O R (Localization.Away a))).action (0, b)).toHom.toCoordinateMap).map
    f.toRingHom = ((E.map (IsScalarTower.toAlgHom O R A)).action (0, b)).toHom.toCoordinateMap at hm
  rw [CoordinateMap.map_comp, CoordinateMap.map_comp, hm,
    Hom.IdempotentImage.overChartTest_inclusion_coordinates,
    Hom.IdempotentImage.overChartTest_projection_coordinates]

end OrderAction.DivisionImage

namespace IdempotentImageCover

variable (E) (C : IdempotentImageCover E.divisionProjector τ)

/-- The atlas of the division image carries the actual induced division order action. -/
def divisionOrder : BasicAtlas.OrderAction B C.atlas where
  chart a := OrderAction.DivisionImage.order
    (E := E.map (IsScalarTower.toAlgHom O R (Localization.Away a.val))) (C.image a).2
  transition A a b ha hb d := by
    let I : (E.map (IsScalarTower.toAlgHom O R (Localization.Away a.val))).DivisionImage _ := (C.image a).2
    let J : (E.map (IsScalarTower.toAlgHom O R (Localization.Away b.val))).DivisionImage _ := (C.image b).2
    let IA : (E.map (IsScalarTower.toAlgHom O R A)).DivisionImage _ := I.overChartTest A ha
    let JA : (E.map (IsScalarTower.toAlgHom O R A)).DivisionImage _ := J.overChartTest A hb
    change (IA.iso JA).hom.comp ((I.order.map (BasicAtlas.coefficientLift (O := O) a.val A ha)).action d) =
      ((J.order.map (BasicAtlas.coefficientLift (O := O) b.val A hb)).action d).comp (IA.iso JA).hom
    rw [I.overChartTest_order_action A ha d, J.overChartTest_order_action A hb d]
    exact (OrderAction.DivisionImage.orderIso (E := E.map (IsScalarTower.toAlgHom O R A)) IA JA).hom.commutes d

end IdempotentImageCover

end Langlands.FormalGroup.ModuleLaw

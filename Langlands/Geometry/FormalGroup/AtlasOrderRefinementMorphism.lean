import Langlands.Geometry.FormalGroup.AtlasOrderRefinement
import Langlands.Geometry.FormalGroup.AtlasRefinementMorphism

/-! # Restriction of order-linear formal atlas maps -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Hom

/-- Restrict the actual formal atlas map, retaining commutation with the whole order. -/
def restrict (f : Hom E E' h) (q : CoverRefinement X) :
    Hom (q.orderAction E) ((q.retarget Y h).orderAction E') rfl :=
  ⟨f.val.restrict q, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.comp
      ((f.val.hom A (sourceChart h.symm (q.source b)) (q.source_unit A b hb)).toHom.toCoordinateMap.comp
        CoordinateMap.id)).comp
      ((((q.orderChart E b).map (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap) =
        ((((q.retarget Y h).orderChart E' b).map
          (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap.comp
            (CoordinateMap.id.comp
              ((f.val.hom A (sourceChart h.symm (q.source b))
                (q.source_unit A b hb)).toHom.toCoordinateMap.comp CoordinateMap.id))
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact (congrArg (fun F => (f.val.hom A (sourceChart h.symm (q.source b))
      (q.source_unit A b hb)).toHom.toCoordinateMap.comp F)
        (q.orderChart_coordinates E A b hb d)).trans
      ((congrArg (fun g => g.toHom.toCoordinateMap)
        (f.commutes A (sourceChart h.symm (q.source b)) (q.source_unit A b hb) d)).trans
          (congrArg (fun F => F.comp (f.val.hom A (sourceChart h.symm (q.source b))
            (q.source_unit A b hb)).toHom.toCoordinateMap)
              ((q.retarget Y h).orderChart_coordinates E' A b hb d).symm))⟩

/-- The underlying formal map is exactly the existing coefficient restriction. -/
@[simp]
theorem restrict_val (f : Hom E E' h) (q : CoverRefinement X) :
    (f.restrict q).val = f.val.restrict q := rfl

/-- Order-linear restriction preserves identity formal maps. -/
@[simp]
theorem restrict_id (E : OrderAction D X) (q : CoverRefinement X) :
    (Hom.id E).restrict q = Hom.id (q.orderAction E) := by
  apply Subtype.ext
  exact BasicAtlas.Hom.restrict_id X q

/-- Order-linear restriction preserves actual formal composition. -/
@[simp]
theorem restrict_comp (g : Hom E' E'' k) (f : Hom E E' h) (q : CoverRefinement X) :
    (g.comp f).restrict q = (g.restrict (q.retarget Y h)).comp (f.restrict q) := by
  apply Subtype.ext
  exact BasicAtlas.Hom.restrict_comp g.val f.val q

/-- Evaluation commutes with the full order-linear restrictions of both families. -/
theorem restrict_onPoints (f : Hom E E' h) (q : CoverRefinement X)
    (A : CommAlgCat.{v} R) (x : E.Point A) :
    (f.restrict q).onPoints A (q.orderOnPoints E A x) =
      (q.retarget Y h).orderOnPoints E' A (f.onPoints A x) :=
  BasicAtlas.Hom.restrict_onPoints f.val q A x

end Hom

namespace Iso

/-- Restrict both actual order-linear formal maps and retain their inverse equations. -/
def restrict (f : Iso E E' h) (q : CoverRefinement X) :
    Iso (q.orderAction E) ((q.retarget Y h).orderAction E') rfl where
  hom := f.hom.restrict q
  inv := f.inv.restrict (q.retarget Y h)
  inv_hom := by
    exact (Hom.restrict_comp f.inv f.hom q).symm.trans
      ((congrArg (fun g => g.restrict q) f.inv_hom).trans (Hom.restrict_id E q))
  hom_inv := by
    exact (Hom.restrict_comp f.hom f.inv (q.retarget Y h)).symm.trans
      ((congrArg (fun g => g.restrict (q.retarget Y h)) f.hom_inv).trans
        (Hom.restrict_id E' (q.retarget Y h)))

/-- The restricted formal isomorphism realizes the full-family refinement square. -/
theorem restrict_onPoints (f : Iso E E' h) (q : CoverRefinement X)
    (A : CommAlgCat.{v} R) (x : E.Point A) :
    (f.restrict q).onPoints A (q.orderPointEquiv E A x) =
      (q.retarget Y h).orderPointEquiv E' A (f.onPoints A x) :=
  Hom.restrict_onPoints f.hom q A x

end Iso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

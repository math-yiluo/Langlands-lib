import Langlands.Geometry.FormalGroup.AtlasBaseChangeMorphism
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangePoints
import Langlands.Geometry.FormalGroup.AtlasOrderMorphism

/-! # Coefficient extension of order-linear formal atlas maps -/

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

/-- Equal chart indices give the same actual order-action coordinate series. -/
theorem testOrderChart_coordinates_eq (E : OrderAction D X) (A : CommAlgCat.{v} R)
    (a b : X.opens) (ha : IsUnit (algebraMap R A a.val))
    (hb : IsUnit (algebraMap R A b.val)) (e : a = b) (d : D) :
    (((E.chart a).map (coefficientLift (O := O) a.val A ha)).action d).toHom.toCoordinateMap =
      (((E.chart b).map (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap := by
  cases e
  rfl

/-- The transported source chart has the original source's order-action series. -/
theorem baseSourceOrderChart_coordinates (E : OrderAction D X) (S : CommAlgCat.{v} R)
    (h : X.opens = Y.opens) (A : CommAlgCat.{v} S) (b : Y.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) (d : D) :
    (((E.baseOrderChart S (sourceChart (baseOpens_eq S h) b)).map
      (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
      (((E.chart (sourceChart h (Y.baseSource S b))).map
        (coefficientLift (O := O) (Y.baseSource S b).val (restrictTest S A)
          (Y.baseSource_unit S A b hb))).action d).toHom.toCoordinateMap :=
  (E.baseOrderChart_coordinates S A (sourceChart (baseOpens_eq S h) b) hb d).trans
    (E.testOrderChart_coordinates_eq (restrictTest S A) _ _ _ _
      (baseSource_sourceChart S h b) d)

namespace Hom

/-- Extend an actual formal atlas map, retaining commutation with the entire order. -/
def baseChange (f : Hom E E' h) (S : CommAlgCat.{v} R) :
    Hom (E.baseChange S) (E'.baseChange S) (baseOpens_eq S h) :=
  ⟨f.val.baseChange S, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.comp
      ((f.val.hom (restrictTest S A) (Y.baseSource S b)
        (Y.baseSource_unit S A b hb)).toHom.toCoordinateMap.comp CoordinateMap.id)).comp
      ((((E.baseOrderChart S (sourceChart (baseOpens_eq S h) b)).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap) =
      ((((E'.baseOrderChart S b).map (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap).comp
        (CoordinateMap.id.comp
          ((f.val.hom (restrictTest S A) (Y.baseSource S b)
            (Y.baseSource_unit S A b hb)).toHom.toCoordinateMap.comp CoordinateMap.id))
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact (congrArg (fun F : CoordinateMap A σ σ =>
      (f.val.hom (restrictTest S A) (Y.baseSource S b)
        (Y.baseSource_unit S A b hb)).toHom.toCoordinateMap.comp F)
          (E.baseSourceOrderChart_coordinates S h A b hb d)).trans
      ((congrArg (fun g => g.toHom.toCoordinateMap)
        (f.commutes (restrictTest S A) (Y.baseSource S b)
          (Y.baseSource_unit S A b hb) d)).trans
        (congrArg (fun F : CoordinateMap A τ τ => F.comp
          (f.val.hom (restrictTest S A) (Y.baseSource S b)
            (Y.baseSource_unit S A b hb)).toHom.toCoordinateMap)
              (E'.baseOrderChart_coordinates S A b hb d).symm))⟩

/-- Forgetting the order recovers exactly the previously constructed formal base change. -/
@[simp]
theorem baseChange_val (f : Hom E E' h) (S : CommAlgCat.{v} R) :
    (f.baseChange S).val = f.val.baseChange S := rfl

/-- Order-linear coefficient extension preserves identity formal maps. -/
@[simp]
theorem baseChange_id (E : OrderAction D X) (S : CommAlgCat.{v} R) :
    (Hom.id E).baseChange S = Hom.id (E.baseChange S) := by
  apply Subtype.ext
  exact BasicAtlas.Hom.baseChange_id X S

/-- Order-linear coefficient extension preserves actual formal composition. -/
@[simp]
theorem baseChange_comp (g : Hom E' E'' k) (f : Hom E E' h) (S : CommAlgCat.{v} R) :
    (g.comp f).baseChange S = (g.baseChange S).comp (f.baseChange S) := by
  apply Subtype.ext
  exact BasicAtlas.Hom.baseChange_comp g.val f.val S

/-- Evaluation commutes with the order-linear comparison of complete compatible families. -/
theorem baseChange_onPoints (f : Hom E E' h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (x : E.Point (restrictTest S A)) :
    (f.baseChange S).onPoints A (E.toBaseChangePoints S A x) =
      E'.toBaseChangePoints S A (f.onPoints (restrictTest S A) x) :=
  BasicAtlas.Hom.baseChange_onPoints f.val S A x

/-- The inverse complete-family comparison also commutes with the order-linear formal map. -/
theorem baseChange_fromPoints (f : Hom E E' h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (y : (E.baseChange S).Point A) :
    f.onPoints (restrictTest S A) ((E.baseChangePointEquiv S A).symm y) =
      (E'.baseChangePointEquiv S A).symm ((f.baseChange S).onPoints A y) :=
  BasicAtlas.Hom.baseChange_fromPoints f.val S A y

end Hom

namespace Iso

/-- Extend both actual order-linear formal maps, retaining the formal inverse equations. -/
def baseChange (f : Iso E E' h) (S : CommAlgCat.{v} R) :
    Iso (E.baseChange S) (E'.baseChange S) (baseOpens_eq S h) where
  hom := f.hom.baseChange S
  inv := f.inv.baseChange S
  inv_hom := (Hom.baseChange_comp f.inv f.hom S).symm.trans
    ((congrArg (fun g => g.baseChange S) f.inv_hom).trans (Hom.baseChange_id E S))
  hom_inv := (Hom.baseChange_comp f.hom f.inv S).symm.trans
    ((congrArg (fun g => g.baseChange S) f.hom_inv).trans (Hom.baseChange_id E' S))

/-- The extended formal isomorphism realizes the order-linear full-family comparison square. -/
theorem baseChange_onPoints (f : Iso E E' h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (x : E.Point (restrictTest S A)) :
    (f.baseChange S).onPoints A (E.baseChangePointEquiv S A x) =
      E'.baseChangePointEquiv S A (f.onPoints (restrictTest S A) x) :=
  f.hom.baseChange_onPoints S A x

/-- The inverse family comparisons realize the reverse order-linear isomorphism square. -/
theorem baseChange_fromPoints (f : Iso E E' h) (S : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) (y : (E.baseChange S).Point A) :
    f.onPoints (restrictTest S A) ((E.baseChangePointEquiv S A).symm y) =
      (E'.baseChangePointEquiv S A).symm ((f.baseChange S).onPoints A y) :=
  f.hom.baseChange_fromPoints S A y

end Iso

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

import Langlands.Geometry.FormalGroup.AtlasOrderComparisonBaseChangeRefinement
import Langlands.Geometry.FormalGroup.SpecialAtlas
import Langlands.Geometry.FormalGroup.AtlasOrderRationalTransition

/-! # Actual comparison isomorphisms between specified original test charts -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- An actual refined comparison, transported to specified original charts on the same test. -/
def testIso (c : Comparison E E') (A : CommAlgCat.{v} R)
    (b : c.right.opens) (hb : IsUnit (algebraMap R A b.val))
    (x : X.opens) (y : Y.opens)
    (hx : IsUnit (algebraMap R A x.val)) (hy : IsUnit (algebraMap R A y.val)) :
    ModuleLaw.OrderAction.Iso
      ((E.chart x).map (coefficientLift (O := O) x.val A hx))
      ((E'.chart y).map (coefficientLift (O := O) y.val A hy)) :=
  let a := sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b
  (((E.transitionIso A x (c.left.source a) hx (c.left.source_unit A a hb)).trans
    (c.left.orderChartIso E A a hb).symm).trans
      (c.coordinateIso.onChart A b hb)).trans
        ((c.right.orderChartIso E' A b hb).trans
          (E'.transitionIso A (c.right.source b) y (c.right.source_unit A b hb) hy))

/-- The complete test comparison series is the original comparison series with its outer transitions. -/
theorem testIso_hom_coordinates (c : Comparison E E') (A : CommAlgCat.{v} R)
    (b : c.right.opens) (hb : IsUnit (algebraMap R A b.val))
    (x : X.opens) (y : Y.opens)
    (hx : IsUnit (algebraMap R A x.val)) (hy : IsUnit (algebraMap R A y.val)) :
    (c.testIso A b hb x y hx hy).hom.val.toHom.toCoordinateMap =
      ((Y.transition A (c.right.source b) y (c.right.source_unit A b hb) hy).hom.toHom.toCoordinateMap.comp
        (c.coordinateIso.hom.val.hom A b hb).toHom.toCoordinateMap).comp
          (X.transition A x (c.left.source
            (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b)) hx
              (c.left.source_unit A
                (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b) hb)).hom.toHom.toCoordinateMap := by
  change ((Y.transition A (c.right.source b) y _ _).hom.toHom.toCoordinateMap.comp
    CoordinateMap.id).comp
      ((c.coordinateIso.hom.val.hom A b hb).toHom.toCoordinateMap.comp
        (CoordinateMap.id.comp (X.transition A x _ _ _).hom.toHom.toCoordinateMap)) = _
  simp only [CoordinateMap.comp_id, CoordinateMap.id_comp, CoordinateMap.comp_assoc]

/-- The whole actual formal comparison on fixed original test charts is independent of the finer chart. -/
theorem testIso_independent (c : Comparison E E') (A : CommAlgCat.{v} R)
    (a b : c.right.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (x : X.opens) (y : Y.opens)
    (hx : IsUnit (algebraMap R A x.val)) (hy : IsUnit (algebraMap R A y.val)) :
    c.testIso A a ha x y hx hy = c.testIso A b hb x y hx hy := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  exact (c.testIso_hom_coordinates A a ha x y hx hy).trans
    ((c.coordinate_transport_independent A a b ha hb x y hx hy).trans
      (c.testIso_hom_coordinates A b hb x y hx hy).symm)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

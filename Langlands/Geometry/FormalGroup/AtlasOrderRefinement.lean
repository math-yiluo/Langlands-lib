import Langlands.Geometry.FormalGroup.AtlasRefinementPoints
import Langlands.Geometry.FormalGroup.AtlasOrderMorphism

/-! # Order actions and full-family descent under principal-cover refinement -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {X : BasicAtlas O R σ} (q : CoverRefinement X) (E : OrderAction D X)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Map the actual order endomorphisms from the selected original chart. -/
def orderChart (b : q.opens) : ModuleLaw.OrderAction D (q.chart b) :=
  (E.chart (q.source b)).map (q.chartCoefficient b)

/-- Both coefficient routes give the same actual order endomorphism series. -/
theorem orderChart_coordinates (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) (d : D) :
    (((q.orderChart E b).map (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
      (((E.chart (q.source b)).map
        (coefficientLift (O := O) (q.source b).val A
          (q.source_unit A b hb))).action d).toHom.toCoordinateMap := by
  change (((E.chart (q.source b)).action d).toHom.toCoordinateMap.map
    (q.chartCoefficient b).toRingHom).map
      (coefficientLift (O := O) b.val A hb).toRingHom = _
  rw [CoordinateMap.map_ringHom_comp, q.coefficient_comp]
  rfl

/-- The actual formal chart identification commutes with the entire order. -/
def orderChartIso (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    ModuleLaw.OrderAction.Iso
      ((q.orderChart E b).map (coefficientLift (O := O) b.val A hb))
      ((E.chart (q.source b)).map
        (coefficientLift (O := O) (q.source b).val A (q.source_unit A b hb))) where
  hom := ⟨(q.chartIso A b hb).hom, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((((q.orderChart E b).map _).action d).toHom.toCoordinateMap) =
        ((((E.chart (q.source b)).map _).action d).toHom.toCoordinateMap).comp
          CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, q.orderChart_coordinates]⟩
  inv := ⟨(q.chartIso A b hb).inv, by
    intro d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change CoordinateMap.id.comp
      ((((E.chart (q.source b)).map _).action d).toHom.toCoordinateMap) =
        ((((q.orderChart E b).map _).action d).toHom.toCoordinateMap).comp
          CoordinateMap.id
    rw [CoordinateMap.id_comp, CoordinateMap.comp_id, q.orderChart_coordinates]⟩
  inv_hom := by
    apply Subtype.ext
    exact (q.chartIso A b hb).inv_hom
  hom_inv := by
    apply Subtype.ext
    exact (q.chartIso A b hb).hom_inv

/-- The restricted formal order action commutes with the refined transitions. -/
theorem orderTransition (A : CommAlgCat.{v} R) (a b : q.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (d : D) :
    (q.transition A a b ha hb).hom.comp
      (((q.orderChart E a).map (coefficientLift (O := O) a.val A ha)).action d) =
        (((q.orderChart E b).map (coefficientLift (O := O) b.val A hb)).action d).comp
          (q.transition A a b ha hb).hom := by
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change (q.transition A a b ha hb).hom.toHom.toCoordinateMap.comp
    ((((q.orderChart E a).map _).action d).toHom.toCoordinateMap) =
      ((((q.orderChart E b).map _).action d).toHom.toCoordinateMap).comp
        (q.transition A a b ha hb).hom.toHom.toCoordinateMap
  rw [q.transition_coordinates, q.orderChart_coordinates, q.orderChart_coordinates]
  exact congrArg (fun f => f.toHom.toCoordinateMap)
    (E.transition A (q.source a) (q.source b)
      (q.source_unit A a ha) (q.source_unit A b hb) d)

/-- The actual formal order action on the finer atlas. -/
def orderAction : OrderAction D q.atlas where
  chart := q.orderChart E
  transition := q.orderTransition E

/-- Evaluation of the formal chart identification is linear over the full order. -/
def orderChartEquiv (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    (q.orderAction E).ChartPoint A b hb ≃ₗ[D]
      E.ChartPoint A (q.source b) (q.source_unit A b hb) :=
  (q.orderChartIso E A b hb).onPoints

@[simp]
theorem orderChartEquiv_apply (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (x : (q.orderAction E).ChartPoint A b hb) :
    q.orderChartEquiv E A b hb x = x := by
  change SeriesPoint.eval CoordinateMap.id x = x
  exact SeriesPoint.eval_id x

@[simp]
theorem orderChartEquiv_symm_apply (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val))
    (x : E.ChartPoint A (q.source b) (q.source_unit A b hb)) :
    (q.orderChartEquiv E A b hb).symm x = x := by
  change SeriesPoint.eval CoordinateMap.id x = x
  exact SeriesPoint.eval_id x

/-- The identity tuple function with the order-linearity of the formal comparison. -/
def orderChartMap (A : CommAlgCat.{v} R) (b : q.opens)
    (hb : IsUnit (algebraMap R A b.val)) :
    E.ChartPoint A (q.source b) (q.source_unit A b hb) →ₗ[D]
      (q.orderAction E).ChartPoint A b hb :=
  (q.orderChartEquiv E A b hb).symm.toLinearMap.copy (fun x => x)
    (funext (fun x => (q.orderChartEquiv_symm_apply E A b hb x).symm))

/-- Restriction of complete compatible families respects every order endomorphism. -/
def orderOnPoints (A : CommAlgCat.{v} R) :
    E.Point A →ₗ[D] (q.orderAction E).Point A where
  toFun := q.onPoints A
  map_add' := (q.onPoints A).map_add
  map_smul' d x := by
    apply Subtype.ext
    funext t
    exact (q.orderChartMap E t.algebra t.chart t.isUnit).map_smul d
      (x.val (q.restrictTest t))

@[simp]
theorem orderOnPoints_apply (A : CommAlgCat.{v} R) (x : E.Point A)
    (t : q.atlas.ChartTest A) :
    (q.orderOnPoints E A x).val t = x.val (q.restrictTest t) := rfl

/-- Actual local coefficient gluing is inverse to the full order-linear restriction. -/
def orderPointEquiv (A : CommAlgCat.{v} R) :
    E.Point A ≃ₗ[D] (q.orderAction E).Point A :=
  { q.orderOnPoints E A with
    invFun := q.fromPoints
    left_inv := q.from_onPoints A
    right_inv := q.on_fromPoints A }

@[simp]
theorem orderPointEquiv_apply (A : CommAlgCat.{v} R) (x : E.Point A)
    (t : q.atlas.ChartTest A) :
    (q.orderPointEquiv E A x).val t = x.val (q.restrictTest t) := rfl

@[simp]
theorem orderPointEquiv_symm_apply (A : CommAlgCat.{v} R)
    (y : (q.orderAction E).Point A) (t : X.ChartTest A) :
    ((q.orderPointEquiv E A).symm y).val t = q.gluedValue y t := rfl

/-- The full order-linear family restriction commutes with coefficient maps. -/
theorem orderOnPoints_natural {A B : CommAlgCat.{v} R} (φ : A ⟶ B)
    (x : E.Point A) :
    (q.orderAction E).mapPoints φ (q.orderOnPoints E A x) =
      q.orderOnPoints E B (E.mapPoints φ x) :=
  q.onPoints_natural φ x

/-- A constructed natural isomorphism of the full order-module point functors. -/
def orderPointFunctorIso : E.pointFunctor ≅ (q.orderAction E).pointFunctor :=
  NatIso.ofComponents (fun A => (q.orderPointEquiv E A).toModuleIso) (by
    intro A B φ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact q.orderOnPoints_natural E φ x)

/-- Restrict the same actual comparison to nilpotent coefficient tests. -/
def orderNilpPointFunctorIso (π : R) :
    E.nilpPointFunctor π ≅ (q.orderAction E).nilpPointFunctor π :=
  Functor.isoWhiskerLeft (Nilp.forget R π) (q.orderPointFunctorIso E)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

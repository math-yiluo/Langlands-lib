import Langlands.Geometry.FormalGroup.AtlasRefinementBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderBaseChangeMorphism
import Langlands.Geometry.FormalGroup.AtlasOrderRefinement

/-! # Order-linear refinement and coefficient-extension compatibility -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ : Type} [Finite σ]
variable {X : BasicAtlas O R σ} (q : CoverRefinement X) (E : OrderAction D X)
variable (S : CommAlgCat.{v} R)

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Extending the finer action retains the original-source order endomorphism series. -/
theorem baseLeftOrderChart_coordinates (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) (d : D) :
    ((((q.orderAction E).baseOrderChart S b).map
      (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
        (((E.chart (q.baseOriginalSource S b)).map
          (coefficientLift (O := O) (q.baseOriginalSource S b).val (BasicAtlas.restrictTest S A)
            (q.baseOriginal_unit S A b hb))).action d).toHom.toCoordinateMap :=
  ((q.orderAction E).baseOrderChart_coordinates S A b hb d).trans
    (q.orderChart_coordinates E (BasicAtlas.restrictTest S A) (q.atlas.baseSource S b)
      (q.atlas.baseSource_unit S A b hb) d)

/-- Refining the extended action retains the selected-source order endomorphism series. -/
theorem baseRightOrderChart_coordinates (A : CommAlgCat.{v} S) (b : q.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S A b.val)) (d : D) :
    ((((q.baseChange S).orderChart (E.baseChange S) b).map
      (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
        (((E.chart (q.baseSelectedSource S b)).map
          (coefficientLift (O := O) (q.baseSelectedSource S b).val (BasicAtlas.restrictTest S A)
            (q.baseSelected_unit S A b hb))).action d).toHom.toCoordinateMap :=
  ((q.baseChange S).orderChart_coordinates (E.baseChange S) A b hb d).trans
    (E.baseOrderChart_coordinates S A ((q.baseChange S).source b)
      ((q.baseChange S).source_unit A b hb) d)

/-- The actual refinement base-change comparison commutes with every order element. -/
def orderBaseChangeHom :
    OrderAction.Hom ((q.orderAction E).baseChange S)
      ((q.baseChange S).orderAction (E.baseChange S)) rfl :=
  ⟨q.baseChangeHom S, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (q.baseChangeChartIso S A b hb).hom.toHom.toCoordinateMap.comp
      ((((q.orderAction E).baseOrderChart S b).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
      ((((q.baseChange S).orderChart (E.baseChange S) b).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap.comp
          (q.baseChangeChartIso S A b hb).hom.toHom.toCoordinateMap
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (q.baseChangeChartIso_coordinates S A b hb)
      (q.baseLeftOrderChart_coordinates E S A b hb d)).trans
      ((congrArg (fun f => f.toHom.toCoordinateMap)
        (E.transition (BasicAtlas.restrictTest S A)
          (q.baseOriginalSource S b) (q.baseSelectedSource S b)
          (q.baseOriginal_unit S A b hb) (q.baseSelected_unit S A b hb) d)).trans
        (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
          (q.baseRightOrderChart_coordinates E S A b hb d)
          (q.baseChangeChartIso_coordinates S A b hb)).symm)⟩

/-- Forgetting the order gives exactly the original formal comparison. -/
@[simp]
theorem orderBaseChangeHom_val :
    (q.orderBaseChangeHom E S).val = q.baseChangeHom S := rfl

/-- The reverse formal refinement comparison also commutes with the entire order. -/
def orderBaseChangeInv :
    OrderAction.Hom ((q.baseChange S).orderAction (E.baseChange S))
      ((q.orderAction E).baseChange S) rfl :=
  ⟨q.baseChangeInv S, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (q.baseChangeInvChartIso S A b hb).hom.toHom.toCoordinateMap.comp
      ((((q.baseChange S).orderChart (E.baseChange S) b).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
      ((((q.orderAction E).baseOrderChart S b).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap.comp
          (q.baseChangeInvChartIso S A b hb).hom.toHom.toCoordinateMap
    exact (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
      (q.baseChangeInvChartIso_coordinates S A b hb)
      (q.baseRightOrderChart_coordinates E S A b hb d)).trans
      ((congrArg (fun f => f.toHom.toCoordinateMap)
        (E.transition (BasicAtlas.restrictTest S A)
          (q.baseSelectedSource S b) (q.baseOriginalSource S b)
          (q.baseSelected_unit S A b hb) (q.baseOriginal_unit S A b hb) d)).trans
        (congrArg₂ (fun F G : CoordinateMap A σ σ => F.comp G)
          (q.baseLeftOrderChart_coordinates E S A b hb d)
          (q.baseChangeInvChartIso_coordinates S A b hb)).symm)⟩

/-- Forgetting the order gives exactly the reverse formal comparison. -/
@[simp]
theorem orderBaseChangeInv_val :
    (q.orderBaseChangeInv E S).val = q.baseChangeInv S := rfl

/-- Refinement and coefficient extension commute as actual order-linear formal atlases. -/
def orderBaseChangeIso :
    OrderAction.Iso ((q.orderAction E).baseChange S)
      ((q.baseChange S).orderAction (E.baseChange S)) rfl where
  hom := q.orderBaseChangeHom E S
  inv := q.orderBaseChangeInv E S
  inv_hom := by
    apply Subtype.ext
    exact (q.baseChangeIso S).inv_hom
  hom_inv := by
    apply Subtype.ext
    exact (q.baseChangeIso S).hom_inv

/-- The order-linear formal comparison realizes the full compatible-family square. -/
theorem orderBaseChange_onPoints (A : CommAlgCat.{v} S)
    (x : E.Point (BasicAtlas.restrictTest S A)) :
    (q.orderBaseChangeIso E S).onPoints A
      ((q.orderAction E).toBaseChangePoints S A (q.orderOnPoints E (BasicAtlas.restrictTest S A) x)) =
        (q.baseChange S).orderOnPoints (E.baseChange S) A (E.toBaseChangePoints S A x) :=
  q.baseChange_onPoints S A x

/-- The inverse order-linear formal comparison realizes the reverse family square. -/
theorem orderBaseChange_inv_onPoints (A : CommAlgCat.{v} S)
    (x : E.Point (BasicAtlas.restrictTest S A)) :
    ((q.orderBaseChangeIso E S).onPoints A).symm
      ((q.baseChange S).orderOnPoints (E.baseChange S) A (E.toBaseChangePoints S A x)) =
        (q.orderAction E).toBaseChangePoints S A
          (q.orderOnPoints E (BasicAtlas.restrictTest S A) x) :=
  q.baseChange_inv_onPoints S A x

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

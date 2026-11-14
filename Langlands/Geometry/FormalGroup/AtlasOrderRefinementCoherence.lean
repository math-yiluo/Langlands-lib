import Langlands.Geometry.FormalGroup.AtlasOrderRefinementMorphism
import Langlands.Geometry.FormalGroup.AtlasRefinementSource

/-! # Formal order-linear coherence for actual atlas refinements -/

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

/-- Direct and successive coefficient restriction agree on every order endomorphism. -/
theorem compOrderChart_coordinates (r : CoverRefinement q.atlas)
    (A : CommAlgCat.{v} R) (b : r.opens)
    (hb : IsUnit (algebraMap R A b.val)) (d : D) :
    ((((q.comp r).orderChart E b).map
      (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
        (((r.orderChart (q.orderAction E) b).map
          (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap :=
  ((q.comp r).orderChart_coordinates E A b hb d).trans
    ((r.orderChart_coordinates (q.orderAction E) A b hb d).trans
      (q.orderChart_coordinates E A (r.source b) (r.source_unit A b hb) d)).symm

/-- The actual direct-to-successive formal comparison commutes with the order. -/
def orderCompHom (r : CoverRefinement q.atlas) :
    OrderAction.Hom ((q.comp r).orderAction E) (r.orderAction (q.orderAction E)) rfl :=
  ⟨q.compHom r, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change ((CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id).comp
      ((((q.comp r).orderChart E b).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
          (((r.orderChart (q.orderAction E) b).map
            (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap.comp
              ((CoordinateMap.id.comp CoordinateMap.id).comp CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact q.compOrderChart_coordinates E r A b hb d⟩

/-- The actual reverse formal comparison also commutes with the order. -/
def orderCompInv (r : CoverRefinement q.atlas) :
    OrderAction.Hom (r.orderAction (q.orderAction E)) ((q.comp r).orderAction E) rfl :=
  ⟨q.compInv r, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    change (CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id)).comp
      (((r.orderChart (q.orderAction E) b).map
        (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
          ((((q.comp r).orderChart E b).map
            (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap.comp
              (CoordinateMap.id.comp (CoordinateMap.id.comp CoordinateMap.id))
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact (q.compOrderChart_coordinates E r A b hb d).symm⟩

/-- Direct and successive restriction are actually formally order-linearly isomorphic. -/
def orderCompIso (r : CoverRefinement q.atlas) :
    OrderAction.Iso ((q.comp r).orderAction E) (r.orderAction (q.orderAction E)) rfl where
  hom := q.orderCompHom E r
  inv := q.orderCompInv E r
  inv_hom := by
    apply Subtype.ext
    exact (q.compIso r).inv_hom
  hom_inv := by
    apply Subtype.ext
    exact (q.compIso r).hom_inv

/-- The order-linear formal comparison realizes direct versus successive family restriction. -/
theorem orderComp_onPoints (r : CoverRefinement q.atlas)
    (A : CommAlgCat.{v} R) (x : E.Point A) :
    (q.orderCompIso E r).onPoints A ((q.comp r).orderOnPoints E A x) =
      r.orderOnPoints (q.orderAction E) A (q.orderOnPoints E A x) :=
  q.comp_onPoints r A x

variable (r : CoverRefinement X) (h : q.opens = r.opens)

/-- Changing selected original charts uses their actual order-compatible transition. -/
def orderSourceHom :
    OrderAction.Hom (q.orderAction E) (r.orderAction E) h :=
  ⟨q.sourceHom r h, by
    intro A b hb d
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    let a := sourceChart (X := q.atlas) (Y := r.atlas) h b
    let T := (X.transition A (q.source a) (r.source b)
      (q.source_unit A a hb) (r.source_unit A b hb)).hom.toHom.toCoordinateMap
    change ((CoordinateMap.id.comp T).comp CoordinateMap.id).comp
      (((q.orderChart E a).map (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap =
        (((r.orderChart E b).map
          (coefficientLift (O := O) b.val A hb)).action d).toHom.toCoordinateMap.comp
            ((CoordinateMap.id.comp T).comp CoordinateMap.id)
    simp only [CoordinateMap.id_comp, CoordinateMap.comp_id]
    exact (congrArg (fun F => T.comp F) (q.orderChart_coordinates E A a hb d)).trans
      ((congrArg (fun g => g.toHom.toCoordinateMap)
        (E.transition A (q.source a) (r.source b)
          (q.source_unit A a hb) (r.source_unit A b hb) d)).trans
            (congrArg (fun F => F.comp T) (r.orderChart_coordinates E A b hb d).symm))⟩

/-- Comparing the same source choice with itself is the identity order-linear formal map. -/
theorem orderSourceHom_id : q.orderSourceHom E q rfl = OrderAction.Hom.id (q.orderAction E) := by
  apply Subtype.ext
  exact q.sourceHom_id

/-- Source-choice comparisons compose as actual order-linear formal maps. -/
theorem orderSourceHom_comp (s : CoverRefinement X) (k : r.opens = s.opens) :
    (r.orderSourceHom E s k).comp (q.orderSourceHom E r h) =
      q.orderSourceHom E s (h.trans k) := by
  apply Subtype.ext
  exact q.sourceHom_comp r h s k

/-- Different source choices on the same finer cover give an actual order-linear isomorphism. -/
def orderSourceIso : OrderAction.Iso (q.orderAction E) (r.orderAction E) h where
  hom := q.orderSourceHom E r h
  inv := r.orderSourceHom E q h.symm
  inv_hom := (q.orderSourceHom_comp E r h q h.symm).trans (q.orderSourceHom_id E)
  hom_inv := (r.orderSourceHom_comp E q h.symm r h).trans (r.orderSourceHom_id E)

/-- Source-choice comparison identifies restrictions of every complete order-module family. -/
theorem orderSource_onPoints (A : CommAlgCat.{v} R) (x : E.Point A) :
    (q.orderSourceIso E r h).onPoints A (q.orderOnPoints E A x) =
      r.orderOnPoints E A x :=
  q.source_onPoints r h A x

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.CoverRefinement

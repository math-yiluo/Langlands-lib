import Langlands.Geometry.FormalGroup.AtlasOrderComparisonInverse

/-! # Refinement and coefficient extension of a specified comparison -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}

attribute [local instance] coefficientAlgebra coefficientScalarTower

set_option backward.isDefEq.respectTransparency false in
/-- Transporting a chart comparison to fixed original charts is independent of its finer chart. -/
theorem coordinate_transport_independent (c : Comparison E E')
    (A : CommAlgCat.{v} R) (a b : c.right.opens)
    (ha : IsUnit (algebraMap R A a.val)) (hb : IsUnit (algebraMap R A b.val))
    (x : X.opens) (y : Y.opens)
    (hx : IsUnit (algebraMap R A x.val)) (hy : IsUnit (algebraMap R A y.val)) :
    ((Y.transition A (c.right.source a) y (c.right.source_unit A a ha) hy).hom.toHom.toCoordinateMap.comp
      (c.coordinateIso.hom.val.hom A a ha).toHom.toCoordinateMap).comp
        (X.transition A x (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a))
          hx (c.left.source_unit A (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a) ha)).hom.toHom.toCoordinateMap =
    ((Y.transition A (c.right.source b) y (c.right.source_unit A b hb) hy).hom.toHom.toCoordinateMap.comp
      (c.coordinateIso.hom.val.hom A b hb).toHom.toCoordinateMap).comp
        (X.transition A x (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b))
          hx (c.left.source_unit A (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b) hb)).hom.toHom.toCoordinateMap := by
  have ht := congrArg (fun f => f.toHom.toCoordinateMap)
    (c.coordinateIso.hom.val.transition A a b ha hb)
  change (c.right.transition A a b ha hb).hom.toHom.toCoordinateMap.comp
      (c.coordinateIso.hom.val.hom A a ha).toHom.toCoordinateMap =
    (c.coordinateIso.hom.val.hom A b hb).toHom.toCoordinateMap.comp
      (c.left.transition A (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a) (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b)
        ha hb).hom.toHom.toCoordinateMap at ht
  dsimp only [CoverRefinement.atlas] at ht
  rw [CoverRefinement.transition_coordinates, CoverRefinement.transition_coordinates] at ht
  have hY := congrArg (fun f => f.hom.toHom.toCoordinateMap)
    (Y.transition_cocycle A (c.right.source a) (c.right.source b) y
      (c.right.source_unit A a ha) (c.right.source_unit A b hb) hy)
  have hX := congrArg (fun f => f.hom.toHom.toCoordinateMap)
    (X.transition_cocycle A x (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a))
      (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b)) hx
      (c.left.source_unit A (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a) ha)
      (c.left.source_unit A (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b) hb))
  change (Y.transition A (c.right.source b) y _ _).hom.toHom.toCoordinateMap.comp
      (Y.transition A (c.right.source a) (c.right.source b) _ _).hom.toHom.toCoordinateMap =
    (Y.transition A (c.right.source a) y _ _).hom.toHom.toCoordinateMap at hY
  change (X.transition A (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a))
      (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b)) _ _).hom.toHom.toCoordinateMap.comp
      (X.transition A x (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a)) _ _).hom.toHom.toCoordinateMap =
    (X.transition A x (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b)) _ _).hom.toHom.toCoordinateMap at hX
  rw [← hY]
  simp only [CoordinateMap.comp_assoc]
  rw [← CoordinateMap.comp_assoc
    (Y.transition A (c.right.source a) (c.right.source b) _ _).hom.toHom.toCoordinateMap,
    ht, CoordinateMap.comp_assoc, hX]

/-- Extend the further cover and retain it as a refinement of the extended comparison. -/
def baseChangeRefinement (c : Comparison E E')
    (q : CoverRefinement c.left.atlas) (S : CommAlgCat.{v} R) :
    CoverRefinement (c.left.baseChange S).atlas where
  opens := q.atlas.baseOpens S
  covers := q.atlas.baseOpens_covers S
  source b := (q.baseChange S).source b
  contains b := q.baseImageSource_unit S b

set_option backward.isDefEq.respectTransparency false in
/-- The two construction orders agree through their actual source-choice maps. -/
theorem baseChange_refine_source_square (c : Comparison E E')
    (q : CoverRefinement c.left.atlas) (S : CommAlgCat.{v} R) :
    (((c.refine q).baseChange S).left.orderSourceIso (E.baseChange S)
      ((c.baseChange S).refine (c.baseChangeRefinement q S)).left rfl).trans
        ((c.baseChange S).refine (c.baseChangeRefinement q S)).coordinateIso =
      ((c.refine q).baseChange S).coordinateIso.trans
        (((c.refine q).baseChange S).right.orderSourceIso (E'.baseChange S)
          ((c.baseChange S).refine (c.baseChangeRefinement q S)).right rfl) := by
  apply BasicAtlas.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro B b hb
  change q.atlas.baseOpens S at b
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  dsimp only [BasicAtlas.OrderAction.Iso.trans, BasicAtlas.OrderAction.Hom.comp, BasicAtlas.Hom.comp]
  dsimp only [refine, baseChange, BasicAtlas.OrderAction.Iso.trans,
    BasicAtlas.OrderAction.Iso.symm, BasicAtlas.OrderAction.Hom.comp,
    BasicAtlas.Hom.comp, ModuleLaw.Hom.comp, CommLaw.Hom.comp,
    CoverRefinement.orderCompIso, CoverRefinement.orderCompHom,
    CoverRefinement.orderCompInv, CoverRefinement.compHom, CoverRefinement.compInv,
    CoverRefinement.orderSourceIso, CoverRefinement.orderSourceHom, CoverRefinement.sourceHom,
    CoverRefinement.orderBaseChangeIso, CoverRefinement.orderBaseChangeHom,
    CoverRefinement.orderBaseChangeInv, CoverRefinement.baseChangeHom, CoverRefinement.baseChangeInv,
    BasicAtlas.OrderAction.Iso.baseChange, BasicAtlas.OrderAction.Hom.baseChange,
    BasicAtlas.OrderAction.Iso.restrict, BasicAtlas.OrderAction.Hom.restrict,
    baseChangeRefinement, CoverRefinement.retarget]
  simp only [CoverRefinement.compChartIso_hom_coordinates,
    CoverRefinement.compChartIso_inv_coordinates, CoverRefinement.sourceChartIso_coordinates,
    CoverRefinement.baseChangeChartIso_coordinates, CoverRefinement.baseChangeInvChartIso_coordinates,
    BasicAtlas.Hom.baseChange_coordinates, BasicAtlas.Hom.restrict_coordinates,
    CoordinateMap.id_comp, CoordinateMap.comp_id]
  dsimp only [BasicAtlas.baseChange, CoverRefinement.baseChange, CoverRefinement.atlas]
  simp only [BasicAtlas.baseTransition_coordinates]
  let A := restrictTest S B
  let p := q.atlas.baseSource S b
  have hp : IsUnit (algebraMap R A p.val) := q.atlas.baseSource_unit S B b hb
  let d := q.source p
  have hd : IsUnit (algebraMap R A d.val) := q.source_unit A p hp
  let a := sourceChart (X := c.right.atlas) (Y := c.left.atlas) c.sameCover.symm d
  have ha : IsUnit (algebraMap R A a.val) := hd
  let bs := q.baseImageSource S b
  have hbs : IsUnit (algebraMap S B bs.val) := (q.baseChange S).source_unit B b hb
  let cs := sourceChart (X := c.right.atlas.baseChange S) (Y := c.left.atlas.baseChange S)
    (baseOpens_eq S c.sameCover.symm) bs
  let a' := c.right.atlas.baseSource S cs
  have ha' : IsUnit (algebraMap R A a'.val) := c.right.atlas.baseSource_unit S B cs hbs
  let e := c.left.atlas.baseSource S bs
  have he : IsUnit (algebraMap R A e.val) := c.left.atlas.baseSource_unit S B bs hbs
  let x := (c.left.comp q).baseSelectedSource S b
  have hx : IsUnit (algebraMap R A x.val) := (c.left.comp q).baseSelected_unit S B b hb
  let xm := c.left.baseSelectedSource S bs
  have hxm : IsUnit (algebraMap R A xm.val) := c.left.baseSelected_unit S B bs hbs
  let y := c.right.baseSelectedSource S cs
  have hy : IsUnit (algebraMap R A y.val) := c.right.baseSelected_unit S B cs hbs
  let ym := (c.right.comp (q.retarget c.right.atlas c.sameCover)).baseSelectedSource S b
  have hym : IsUnit (algebraMap R A ym.val) :=
    (c.right.comp (q.retarget c.right.atlas c.sameCover)).baseSelected_unit S B b hb
  change (((Y.transition A (c.right.source a') y (c.right.source_unit A a' ha') hy).hom.toHom.toCoordinateMap.comp
    (c.coordinateIso.hom.val.hom A a' ha').toHom.toCoordinateMap).comp
      (X.transition A xm (c.left.source e) hxm (c.left.source_unit A e he)).hom.toHom.toCoordinateMap).comp
        (X.transition A x xm hx hxm).hom.toHom.toCoordinateMap =
    (Y.transition A ym y hym hy).hom.toHom.toCoordinateMap.comp
      (((Y.transition A (c.right.source a) ym (c.right.source_unit A a ha) hym).hom.toHom.toCoordinateMap.comp
        (c.coordinateIso.hom.val.hom A a ha).toHom.toCoordinateMap).comp
          (X.transition A x (c.left.source d) hx (c.left.source_unit A d hd)).hom.toHom.toCoordinateMap)
  have ee : e = sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a' := by
    exact baseSource_sourceChart S c.sameCover cs
  have dd : d = sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a := by
    apply Subtype.ext
    rfl
  have hX := congrArg (fun f => f.hom.toHom.toCoordinateMap)
    (X.transition_cocycle A x xm (c.left.source e) hx hxm (c.left.source_unit A e he))
  have hY := congrArg (fun f => f.hom.toHom.toCoordinateMap)
    (Y.transition_cocycle A (c.right.source a) ym y
      (c.right.source_unit A a ha) hym hy)
  change (X.transition A xm (c.left.source e) _ _).hom.toHom.toCoordinateMap.comp
      (X.transition A x xm _ _).hom.toHom.toCoordinateMap =
    (X.transition A x (c.left.source e) _ _).hom.toHom.toCoordinateMap at hX
  change (Y.transition A ym y _ _).hom.toHom.toCoordinateMap.comp
      (Y.transition A (c.right.source a) ym _ _).hom.toHom.toCoordinateMap =
    (Y.transition A (c.right.source a) y _ _).hom.toHom.toCoordinateMap at hY
  rw [CoordinateMap.comp_assoc, hX]
  simp only [← CoordinateMap.comp_assoc]
  rw [hY]
  have hXe := X.testTransition_coordinates_eq A x (c.left.source e)
    x (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a'))
    hx (c.left.source_unit A e he) hx
    (c.left.source_unit A (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a') ha')
    rfl (congrArg c.left.source ee)
  have hXd := X.testTransition_coordinates_eq A x (c.left.source d)
    x (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a))
    hx (c.left.source_unit A d hd) hx
    (c.left.source_unit A (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a) ha)
    rfl (congrArg c.left.source dd)
  rw [hXe, hXd]
  exact c.coordinate_transport_independent A a' a ha' ha x y hx hy

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

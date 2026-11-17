import Langlands.Geometry.FormalGroup.AtlasOrderComparisonTest
import Langlands.Geometry.FormalGroup.AtlasOrderComparisonBaseChange

/-! # Actual test-chart comparison through coefficient extension -/

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

set_option backward.isDefEq.respectTransparency false in
/-- The actual extended comparison between fixed test charts is the original test comparison
through the two actual coefficient-chart isomorphisms. -/
theorem testIso_baseChange (c : Comparison E E') (S : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) (b : c.right.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S B b.val))
    (x : X.baseOpens S) (y : Y.baseOpens S)
    (hx : IsUnit (algebraMap S B x.val)) (hy : IsUnit (algebraMap S B y.val)) :
    ((c.baseChange S).testIso B b hb x y hx hy).trans (E'.baseOrderChartIso S B y hy) =
      (E.baseOrderChartIso S B x hx).trans
        (c.testIso (restrictTest S B) (c.right.atlas.baseSource S b)
          (c.right.atlas.baseSource_unit S B b hb) (X.baseSource S x) (Y.baseSource S y)
          (X.baseSource_unit S B x hx) (Y.baseSource_unit S B y hy)) := by
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change CoordinateMap.id.comp
      ((c.baseChange S).testIso B b hb x y hx hy).hom.val.toHom.toCoordinateMap =
    (c.testIso (restrictTest S B) (c.right.atlas.baseSource S b)
      (c.right.atlas.baseSource_unit S B b hb) (X.baseSource S x) (Y.baseSource S y)
      (X.baseSource_unit S B x hx) (Y.baseSource_unit S B y hy)).hom.val.toHom.toCoordinateMap.comp
        CoordinateMap.id
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id, testIso_hom_coordinates]
  dsimp only [baseChange, BasicAtlas.OrderAction.Iso.trans, BasicAtlas.OrderAction.Iso.symm,
    BasicAtlas.OrderAction.Hom.comp, BasicAtlas.Hom.comp,
    CoverRefinement.orderBaseChangeIso, CoverRefinement.orderBaseChangeHom,
    CoverRefinement.orderBaseChangeInv, CoverRefinement.baseChangeHom,
    CoverRefinement.baseChangeInv, BasicAtlas.OrderAction.Iso.baseChange,
    BasicAtlas.OrderAction.Hom.baseChange, ModuleLaw.Hom.comp, CommLaw.Hom.comp]
  simp only [CoverRefinement.baseChangeChartIso_coordinates,
    CoverRefinement.baseChangeInvChartIso_coordinates, BasicAtlas.Hom.baseChange_coordinates]
  dsimp only [BasicAtlas.baseChange, CoverRefinement.baseChange, CoverRefinement.atlas]
  simp only [BasicAtlas.baseTransition_coordinates]
  let A := restrictTest S B
  let bs := sourceChart (X := c.left.atlas.baseChange S) (Y := c.right.atlas.baseChange S)
    (baseOpens_eq S c.sameCover) b
  let a := c.right.atlas.baseSource S b
  have ha : IsUnit (algebraMap R A a.val) := c.right.atlas.baseSource_unit S B b hb
  let l := c.left.baseSelectedSource S bs
  have hl : IsUnit (algebraMap R A l.val) := c.left.baseSelected_unit S B bs hb
  let lo := c.left.baseOriginalSource S bs
  have hlo : IsUnit (algebraMap R A lo.val) := c.left.baseOriginal_unit S B bs hb
  let r := c.right.baseSelectedSource S b
  have hr : IsUnit (algebraMap R A r.val) := c.right.baseSelected_unit S B b hb
  let ro := c.right.baseOriginalSource S b
  have hro : IsUnit (algebraMap R A ro.val) := c.right.baseOriginal_unit S B b hb
  let xx := X.baseSource S x
  have hxx : IsUnit (algebraMap R A xx.val) := X.baseSource_unit S B x hx
  let yy := Y.baseSource S y
  have hyy : IsUnit (algebraMap R A yy.val) := Y.baseSource_unit S B y hy
  have ee : c.left.atlas.baseSource S bs =
      sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a :=
    baseSource_sourceChart S c.sameCover b
  have hX := congrArg (fun z => z.hom.toHom.toCoordinateMap)
    (X.transition_cocycle A xx l lo hxx hl hlo)
  have hY := congrArg (fun z => z.hom.toHom.toCoordinateMap)
    (Y.transition_cocycle A ro r yy hro hr hyy)
  change (X.transition A l lo _ _).hom.toHom.toCoordinateMap.comp
      (X.transition A xx l _ _).hom.toHom.toCoordinateMap =
    (X.transition A xx lo _ _).hom.toHom.toCoordinateMap at hX
  change (Y.transition A r yy _ _).hom.toHom.toCoordinateMap.comp
      (Y.transition A ro r _ _).hom.toHom.toCoordinateMap =
    (Y.transition A ro yy _ _).hom.toHom.toCoordinateMap at hY
  change ((Y.transition A r yy hr hyy).hom.toHom.toCoordinateMap.comp
      (((Y.transition A ro r hro hr).hom.toHom.toCoordinateMap.comp
        (c.coordinateIso.hom.val.hom A a ha).toHom.toCoordinateMap).comp
          (X.transition A l lo hl hlo).hom.toHom.toCoordinateMap)).comp
            (X.transition A xx l hxx hl).hom.toHom.toCoordinateMap = _
  simp only [CoordinateMap.comp_assoc]
  rw [hX, ← CoordinateMap.comp_assoc, hY]
  have hL := X.testTransition_coordinates_eq A xx lo xx
    (c.left.source (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a))
    hxx hlo hxx (c.left.source_unit A
      (sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover a) ha)
    rfl (congrArg c.left.source ee)
  rw [hL]
  rfl

/-- Transport any specified actual original finer-chart comparison between the extended outer charts. -/
def baseChangeOriginalTestIso (c : Comparison E E') (S : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictTest S B) a.val))
    (x : X.baseOpens S) (y : Y.baseOpens S)
    (hx : IsUnit (algebraMap S B x.val)) (hy : IsUnit (algebraMap S B y.val)) :=
  (E.baseOrderChartIso S B x hx).trans
    ((c.testIso (restrictTest S B) a ha (X.baseSource S x) (Y.baseSource S y)
      (X.baseSource_unit S B x hx) (Y.baseSource_unit S B y hy)).trans
        (E'.baseOrderChartIso S B y hy).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The whole extended test comparison equals transport from any supplied original finer chart. -/
theorem testIso_baseChange_eq_original (c : Comparison E E') (S : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) (b : c.right.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S B b.val)) (a : c.right.opens)
    (ha : IsUnit (algebraMap R (restrictTest S B) a.val))
    (x : X.baseOpens S) (y : Y.baseOpens S)
    (hx : IsUnit (algebraMap S B x.val)) (hy : IsUnit (algebraMap S B y.val)) :
    (c.baseChange S).testIso B b hb x y hx hy =
      c.baseChangeOriginalTestIso S B a ha x y hx hy := by
  have h := congrArg (fun z => z.hom.val.toHom.toCoordinateMap)
    (c.testIso_baseChange S B b hb x y hx hy)
  change CoordinateMap.id.comp
      ((c.baseChange S).testIso B b hb x y hx hy).hom.val.toHom.toCoordinateMap =
    (c.testIso (restrictTest S B) (c.right.atlas.baseSource S b)
      (c.right.atlas.baseSource_unit S B b hb) (X.baseSource S x) (Y.baseSource S y)
      (X.baseSource_unit S B x hx) (Y.baseSource_unit S B y hy)).hom.val.toHom.toCoordinateMap.comp
        CoordinateMap.id at h
  simp only [CoordinateMap.id_comp, CoordinateMap.comp_id] at h
  have hi := congrArg (fun z => z.hom.val.toHom.toCoordinateMap)
    (c.testIso_independent (restrictTest S B) (c.right.atlas.baseSource S b) a
      (c.right.atlas.baseSource_unit S B b hb) ha (X.baseSource S x) (Y.baseSource S y)
      (X.baseSource_unit S B x hx) (Y.baseSource_unit S B y hy))
  apply ModuleLaw.OrderAction.Iso.ext_hom
  apply Subtype.ext
  apply ModuleLaw.Hom.ext
  apply CommLaw.Hom.ext
  change ((c.baseChange S).testIso B b hb x y hx hy).hom.val.toHom.toCoordinateMap =
    (CoordinateMap.id.comp
      (c.testIso (restrictTest S B) a ha (X.baseSource S x) (Y.baseSource S y)
        (X.baseSource_unit S B x hx) (Y.baseSource_unit S B y hy)).hom.val.toHom.toCoordinateMap).comp
          CoordinateMap.id
  simpa only [CoordinateMap.id_comp, CoordinateMap.comp_id] using h.trans hi

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

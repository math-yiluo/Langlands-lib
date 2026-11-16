import Langlands.Geometry.FormalGroup.AtlasOrderRationalRestrictionSquare
import Langlands.Geometry.FormalGroup.AtlasOrderComparisonEquivalence
import Langlands.Geometry.FormalGroup.AtlasOrderRationalRefinementComposition
import Langlands.Geometry.FormalGroup.AtlasOrderRationalSourceChoice

/-! # Actual chart squares for refining a specified formal comparison -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Refining the specified comparison gives an actual rational square with its original chart map. -/
def refinementChartSquare (c : BasicAtlas.OrderAction.Comparison E E') (q : CoverRefinement c.left.atlas)
    (B : CommAlgCat.{v} R) (b : q.opens) (hb : IsUnit (algebraMap R B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := F)
      (((c.left.comp q).orderChart E b).map (coefficientLift (O := O) b.val B hb))
      (((c.right.comp (q.retarget c.right.atlas c.sameCover)).orderChart E' b).map
        (coefficientLift (O := O) b.val B hb))
      (((c.right.orderAction E').chart
        (sourceChart (X := c.right.atlas) (Y := c.left.atlas) c.sameCover.symm (q.source b))).map
          (coefficientLift (O := O) (q.source b).val B (q.source_unit B b hb)))
      (((c.left.orderAction E).chart (q.source b)).map
        (coefficientLift (O := O) (q.source b).val B (q.source_unit B b hb))) where
  top := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
    (c.refine q).coordinateIso).onChart B b hb
  right := (c.right.orderCompQuasi (F := F) E'
    (q.retarget c.right.atlas c.sameCover) B b hb).trans
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        ((q.retarget c.right.atlas c.sameCover).orderChartIso (c.right.orderAction E') B b hb))
  left := (c.left.orderCompQuasi (F := F) E q B b hb).trans
    (ModuleLaw.OrderAction.QuasiIsogeny.ofIso (q.orderChartIso (c.left.orderAction E) B b hb))
  bottom := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F) c.coordinateIso).onChart B
    (sourceChart (X := c.right.atlas) (Y := c.left.atlas) c.sameCover.symm (q.source b))
    (q.source_unit B b hb)
  commutes := by
    let r := q.retarget c.right.atlas c.sameCover
    let cl := c.left.orderCompQuasi (F := F) E q B b hb
    let cr := c.right.orderCompQuasi (F := F) E' r B b hb
    let il := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F)
      (q.orderChartIso (c.left.orderAction E) B b hb)
    let ir := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F)
      (r.orderChartIso (c.right.orderAction E') B b hb)
    let mid := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
      (c.coordinateIso.restrict q)).onChart B b hb
    let old := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F) c.coordinateIso).onChart B
      (sourceChart (X := c.right.atlas) (Y := c.left.atlas) c.sameCover.symm (q.source b))
      (q.source_unit B b hb)
    have hm : mid.trans ir = il.trans old :=
      (congrArg (fun f => (f.onChart B b hb).trans ir)
        (BasicAtlas.OrderAction.QuasiIsogeny.restrict_ofIso
          (F := F) c.coordinateIso q).symm).trans
            ((BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F) c.coordinateIso).restrictionChartSquare
              q B b hb).commutes
    have hn : (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
        (c.refine q).coordinateIso).onChart B b hb = (cl.trans mid).trans cr.symm := by
      apply ModuleLaw.OrderAction.QuasiIsogeny.ext
      apply ModuleLaw.OrderAction.RationalHom.ext
      let fl := (c.left.orderCompIso E q).hom.val.hom B b hb
      let fm := (c.coordinateIso.restrict q).hom.val.hom B b hb
      let fr := (c.right.orderCompIso E' r).inv.val.hom B b hb
      have h₁ := ModuleLaw.RationalHom.ofHom_comp (F := F) fr fm
      have h₂ := ModuleLaw.RationalHom.ofHom_comp (F := F) (fr.comp fm) fl
      have h₃ := ModuleLaw.RationalHom.comp_assoc
        (ModuleLaw.RationalHom.ofHom (F := F) fr)
        (ModuleLaw.RationalHom.ofHom (F := F) fm)
        (ModuleLaw.RationalHom.ofHom (F := F) fl)
      exact h₂.trans ((congrArg (fun k => ModuleLaw.RationalHom.comp k
        (ModuleLaw.RationalHom.ofHom (F := F) fl)) h₁).trans h₃)
    exact (congrArg (fun k => k.trans (cr.trans ir)) hn).trans
      ((ModuleLaw.OrderAction.QuasiIsogeny.trans_symm_trans (cl.trans mid) cr ir).trans
        ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc cl mid ir).trans
          ((congrArg (fun k => cl.trans k) hm).trans
            (ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc cl il old).symm)))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

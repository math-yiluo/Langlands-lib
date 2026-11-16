import Langlands.Geometry.FormalGroup.AtlasOrderRationalRefinement
import Langlands.Geometry.FormalGroup.AtlasOrderQuasiIsogenyCalculus

/-! # Actual rational restriction squares on defined finer formal charts -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual restricted quasi-isogeny is the original chart map through its two formal identifications. -/
theorem onChart_restrict (f : QuasiIsogeny F E E' h) (q : CoverRefinement X)
    (B : CommAlgCat.{v} R) (b : q.opens) (hb : IsUnit (algebraMap R B b.val)) :
    (f.restrict q).onChart B b hb =
      ((ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F)
        (q.orderChartIso E B b hb)).trans
          (f.onChart B (sourceChart (X := Y) (Y := X) h.symm (q.source b))
            (q.source_unit B b hb))).trans
              (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
                ((q.retarget Y h).orderChartIso E' B b hb)).symm := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  exact RationalHom.onChart_restrict f.hom q B b hb

/-- The actual refined and original chart maps form a specified rational commuting square. -/
def restrictionChartSquare (f : QuasiIsogeny F E E' h) (q : CoverRefinement X)
    (B : CommAlgCat.{v} R) (b : q.opens) (hb : IsUnit (algebraMap R B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := F)
      ((q.orderChart E b).map (coefficientLift (O := O) b.val B hb))
      (((q.retarget Y h).orderChart E' b).map (coefficientLift (O := O) b.val B hb))
      ((E'.chart (sourceChart (X := Y) (Y := X) h.symm (q.source b))).map
        (coefficientLift (O := O) (q.source b).val B (q.source_unit B b hb)))
      ((E.chart (q.source b)).map
        (coefficientLift (O := O) (q.source b).val B (q.source_unit B b hb))) where
  top := (f.restrict q).onChart B b hb
  right := ModuleLaw.OrderAction.QuasiIsogeny.ofIso
    ((q.retarget Y h).orderChartIso E' B b hb)
  left := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (q.orderChartIso E B b hb)
  bottom := f.onChart B (sourceChart (X := Y) (Y := X) h.symm (q.source b))
    (q.source_unit B b hb)
  commutes := by
    let s := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F) (q.orderChartIso E B b hb)
    let t := ModuleLaw.OrderAction.QuasiIsogeny.ofIso (F := F)
      ((q.retarget Y h).orderChartIso E' B b hb)
    let g := f.onChart B (sourceChart (X := Y) (Y := X) h.symm (q.source b))
      (q.source_unit B b hb)
    have he : (f.restrict q).onChart B b hb = (s.trans g).trans t.symm :=
      onChart_restrict f q B b hb
    exact (congrArg (fun k => k.trans t) he).trans
      ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc (s.trans g) t.symm t).trans
        ((congrArg (fun k => (s.trans g).trans k)
          (ModuleLaw.OrderAction.QuasiIsogeny.symm_trans_self t)).trans
            (ModuleLaw.OrderAction.QuasiIsogeny.trans_refl (s.trans g))))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

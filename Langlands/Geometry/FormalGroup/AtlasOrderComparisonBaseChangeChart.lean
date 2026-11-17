import Langlands.Geometry.FormalGroup.AtlasOrderComparisonBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderRationalRefinementBaseChange

/-! # Actual rational chart square for coefficient extension of a comparison -/

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

/-- The specified coefficient-extended comparison gives the actual rational square
with extension of its original coordinate isomorphism and both refinement corrections. -/
def baseChangeChartSquare (c : Comparison E E') (S : CommAlgCat.{v} R)
    (B : CommAlgCat.{v} S) (b : c.right.atlas.baseOpens S)
    (hb : IsUnit (algebraMap S B b.val)) :
    ModuleLaw.OrderAction.QuasiIsogeny.CommutingSquare (F := F)
      (((c.left.baseChange S).orderChart (E.baseChange S)
        (sourceChart (X := (c.left.atlas.baseChange S))
          (Y := (c.right.atlas.baseChange S)) (baseOpens_eq S c.sameCover) b)).map
            (coefficientLift (O := O) b.val B hb))
      (((c.right.baseChange S).orderChart (E'.baseChange S) b).map
        (coefficientLift (O := O) b.val B hb))
      ((((c.right.orderAction E').baseChange S).chart b).map
        (coefficientLift (O := O) b.val B hb))
      ((((c.left.orderAction E).baseChange S).chart
        (sourceChart (X := (c.left.atlas.baseChange S))
          (Y := (c.right.atlas.baseChange S)) (baseOpens_eq S c.sameCover) b)).map
            (coefficientLift (O := O) b.val B hb)) where
  top := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
    (c.baseChange S).coordinateIso).onChart B b hb
  right := (c.right.orderBaseChangeQuasi (F := F) E' S B b hb).symm
  left := (c.left.orderBaseChangeQuasi (F := F) E S B
    (sourceChart (X := (c.left.atlas.baseChange S))
      (Y := (c.right.atlas.baseChange S)) (baseOpens_eq S c.sameCover) b) hb).symm
  bottom := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
    (c.coordinateIso.baseChange S)).onChart B b hb
  commutes := by
    let a := sourceChart (X := (c.left.atlas.baseChange S))
      (Y := (c.right.atlas.baseChange S)) (baseOpens_eq S c.sameCover) b
    let ll := c.left.orderBaseChangeQuasi (F := F) E S B a hb
    let rr := c.right.orderBaseChangeQuasi (F := F) E' S B b hb
    let mid := (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
      (c.coordinateIso.baseChange S)).onChart B b hb
    have hn : (BasicAtlas.OrderAction.QuasiIsogeny.ofIso (F := F)
        (c.baseChange S).coordinateIso).onChart B b hb =
          (ll.symm.trans mid).trans rr := by
      apply ModuleLaw.OrderAction.QuasiIsogeny.ext
      apply ModuleLaw.OrderAction.RationalHom.ext
      let fl := (c.left.orderBaseChangeIso E S).inv.val.hom B a hb
      let fm := (c.coordinateIso.baseChange S).hom.val.hom B b hb
      let fr := (c.right.orderBaseChangeIso E' S).hom.val.hom B b hb
      have h₁ := ModuleLaw.RationalHom.ofHom_comp (F := F) fr fm
      have h₂ := ModuleLaw.RationalHom.ofHom_comp (F := F) (fr.comp fm) fl
      have h₃ := ModuleLaw.RationalHom.comp_assoc
        (ModuleLaw.RationalHom.ofHom (F := F) fr)
        (ModuleLaw.RationalHom.ofHom (F := F) fm)
        (ModuleLaw.RationalHom.ofHom (F := F) fl)
      exact h₂.trans ((congrArg (fun k => ModuleLaw.RationalHom.comp k
        (ModuleLaw.RationalHom.ofHom (F := F) fl)) h₁).trans h₃)
    exact (congrArg (fun k => k.trans rr.symm) hn).trans
      ((ModuleLaw.OrderAction.QuasiIsogeny.trans_assoc (ll.symm.trans mid) rr rr.symm).trans
        ((congrArg (fun k => (ll.symm.trans mid).trans k)
          (ModuleLaw.OrderAction.QuasiIsogeny.self_trans_symm rr)).trans
            (ModuleLaw.OrderAction.QuasiIsogeny.trans_refl (ll.symm.trans mid))))

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

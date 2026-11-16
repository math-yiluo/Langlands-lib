import Langlands.Geometry.FormalGroup.AtlasOrderRationalMorphism
import Langlands.Geometry.FormalGroup.OrderQuasiIsogenyCalculus

/-! # Actual rational inverse and composition laws on formal atlas charts -/

noncomputable section

universe u v w z

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

open CategoryTheory

variable {O : Type u} [CommRing O] [IsDomain O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {F : Type z} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ υ : Type} [Finite σ] [Finite τ] [Finite υ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ} {Z : BasicAtlas O R υ}
variable {E : OrderAction D X} {E' : OrderAction D Y} {E'' : OrderAction D Z}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

@[simp]
theorem ofIso_refl (E : OrderAction D X) :
    ofIso (F := F) (Iso.refl E) = refl E := by
  apply ext_hom
  rfl

@[simp]
theorem ofIso_symm (f : Iso E E' h) :
    ofIso (F := F) f.symm = (ofIso f).symm := by
  apply ext_hom
  rfl

@[simp]
theorem ofIso_trans (f : Iso E E' h) (g : Iso E' E'' k) :
    ofIso (F := F) (f.trans g) = (ofIso f).trans (ofIso g) := by
  apply ext_hom
  exact RationalHom.ofHom_comp g.hom f.hom

@[simp]
theorem onChart_refl (E : OrderAction D X) (B : CommAlgCat.{v} R) (b : X.opens)
    (hb : IsUnit (algebraMap R B b.val)) :
    (refl (F := F) E).onChart B b hb =
      ModuleLaw.OrderAction.QuasiIsogeny.refl _ := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  exact RationalHom.onChart_id E B b hb

@[simp]
theorem onChart_symm (f : QuasiIsogeny F E E' h)
    (B : CommAlgCat.{v} R) (b : Y.opens) (hb : IsUnit (algebraMap R B b.val)) :
    f.symm.onChart B (sourceChart (X := X) (Y := Y) h b) hb =
      (f.onChart B b hb).symm := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  rfl

theorem onChart_trans (f : QuasiIsogeny F E E' h) (g : QuasiIsogeny F E' E'' k)
    (B : CommAlgCat.{v} R) (b : Z.opens) (hb : IsUnit (algebraMap R B b.val)) :
    (f.trans g).onChart B b hb =
      (f.onChart B (sourceChart (X := Y) (Y := Z) k b) hb).trans
        (g.onChart B b hb) := by
  apply ModuleLaw.OrderAction.QuasiIsogeny.ext
  exact RationalHom.onChart_comp g.hom f.hom B b hb

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.QuasiIsogeny

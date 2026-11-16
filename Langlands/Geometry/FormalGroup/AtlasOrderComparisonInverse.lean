import Langlands.Geometry.FormalGroup.AtlasOrderComparisonBaseChange
import Langlands.Geometry.FormalGroup.AtlasOrderComparisonEquivalence

/-! # Actual inversion of coefficient-extended formal comparisons -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

open CategoryTheory

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ υ ω : Type} [Finite σ] [Finite τ] [Finite υ] [Finite ω]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {Z : BasicAtlas O R υ} {W : BasicAtlas O R ω}
variable {E : OrderAction D X} {E' : OrderAction D Y}
variable {E'' : OrderAction D Z} {E''' : OrderAction D W}
variable {h : X.opens = Y.opens} {k : Y.opens = Z.opens} {l : Z.opens = W.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

namespace Iso

/-- The actual inverse formal map is determined by a left inverse equation. -/
theorem inv_unique (f : Iso E E' h) (g : Hom E' E h.symm)
    (e : g.comp f.hom = Hom.id E) : g = f.inv := by
  calc
    g = g.comp (Hom.id E') := (Hom.comp_id _).symm
    _ = g.comp (f.hom.comp f.inv) := by rw [f.hom_inv]
    _ = (g.comp f.hom).comp f.inv := (Hom.comp_assoc _ _ _).symm
    _ = f.inv := by rw [e, Hom.id_comp]

@[ext]
theorem ext_hom {f g : Iso E E' h} (e : f.hom = g.hom) : f = g := by
  have ei : f.inv = g.inv := g.inv_unique f.inv (by rw [← e]; exact f.inv_hom)
  cases f
  cases g
  cases e
  cases ei
  rfl

@[simp]
theorem symm_symm (f : Iso E E' h) : f.symm.symm = f := rfl

theorem symm_trans (f : Iso E E' h) (g : Iso E' E'' k) :
    (f.trans g).symm = g.symm.trans f.symm := rfl

theorem trans_assoc (f : Iso E E' h) (g : Iso E' E'' k) (q : Iso E'' E''' l) :
    (f.trans g).trans q = f.trans (g.trans q) := by
  apply ext_hom
  exact (Hom.comp_assoc q.hom g.hom f.hom).symm

@[simp]
theorem baseChange_symm (f : Iso E E' h) (S : CommAlgCat.{v} R) :
    f.symm.baseChange S = (f.baseChange S).symm := by
  apply ext_hom
  rfl

end Iso

namespace Comparison

/-- Coefficient extension reverses the same actual refined formal comparison. -/
theorem baseChange_symm (f : Comparison E E') (S : CommAlgCat.{v} R) :
    f.symm.baseChange S = (f.baseChange S).symm := by
  unfold baseChange symm
  congr 1
  apply Iso.ext_hom
  exact (Hom.comp_assoc (f.left.orderBaseChangeIso E S).hom
    (f.coordinateIso.baseChange S).inv (f.right.orderBaseChangeIso E' S).inv)

end Comparison

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

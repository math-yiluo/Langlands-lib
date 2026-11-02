import Langlands.CategoryTheory.OverTotalPresheaf
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Representing total presheaves and transporting representations -/

universe w v v' u u'

open CategoryTheory CategoryTheory.Category Opposite

noncomputable section

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u} [Category.{v} C] {S : C}
  {G : (Over S)ᵒᵖ ⥤ Type w} {A : Over S}

set_option backward.isDefEq.respectTransparency false in
/-- A representation on a slice represents its total presheaf by the domain. -/
def toOverTotal (e : G.RepresentableBy A) : G.overTotal.RepresentableBy A.left where
  homEquiv {T} :=
    { toFun := fun k ↦ ⟨k ≫ A.hom, e.homEquiv (Over.homMk k rfl)⟩
      invFun := fun x ↦ (e.homEquiv.symm x.2).left
      left_inv := fun k ↦ by simp
      right_inv := fun x ↦ by
        apply OverTotal.ext' (Over.w (e.homEquiv.symm x.2))
        rw [← e.homEquiv_comp]
        apply e.homEquiv.symm.injective
        simp only [Equiv.symm_apply_apply]
        apply Over.OverMorphism.ext
        simp }
  homEquiv_comp {T T'} k g := by
    apply OverTotal.ext' (Category.assoc k g A.hom)
    let B : Over S := Over.mk (k ≫ (g ≫ A.hom))
    let B' : Over S := Over.mk ((k ≫ g) ≫ A.hom)
    let D : Over S := Over.mk (g ≫ A.hom)
    let i : B ⟶ B' := Over.homMk (𝟙 T) (by simp [B, B', Category.assoc])
    let k' : B ⟶ D := Over.homMk k rfl
    let g' : D ⟶ A := Over.homMk g rfl
    let kg' : B' ⟶ A := Over.homMk (k ≫ g) rfl
    change G.map i.op (e.homEquiv kg') = G.map k'.op (e.homEquiv g')
    have h : i ≫ kg' = k' ≫ g' := by
      apply Over.OverMorphism.ext
      change (𝟙 T) ≫ (k ≫ g) = k ≫ g
      exact Category.id_comp _
    exact (e.homEquiv_comp i kg').symm.trans
      ((congrArg e.homEquiv h).trans (e.homEquiv_comp k' g'))

variable {D : Type u'} [Category.{v'} D]
  (E : C ≌ D) {F : Dᵒᵖ ⥤ Type w} {Y : C}

/-- A representation transported across an equivalence of the test categories. -/
def ofEquivalence (e : (E.functor.op ⋙ F).RepresentableBy Y) :
    F.RepresentableBy (E.functor.obj Y) where
  homEquiv {T} := ((E.symm.toAdjunction.homEquiv T Y).symm.trans e.homEquiv).trans
    (F.mapIso (E.counitIso.app T).symm.op).toEquiv
  homEquiv_comp {T T'} k g := by
    dsimp
    rw [E.symm.toAdjunction.homEquiv_naturality_left_symm, e.homEquiv_comp]
    change F.map (E.counitIso.inv.app T).op
        (F.map (E.functor.map (E.inverse.map k)).op _) =
      F.map k.op (F.map (E.counitIso.inv.app T').op _)
    rw [← F.map_comp_apply, ← F.map_comp_apply, ← op_comp, ← op_comp]
    have h := E.counitIso.inv.naturality k
    dsimp only [Functor.id_map, Functor.comp_map] at h
    rw [h]

end CategoryTheory.Functor.RepresentableBy

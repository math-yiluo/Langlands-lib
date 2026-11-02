import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber

/-! # Point fibres after changing the atlas object by an actual isomorphism -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPointFiberObjectIso

open Langlands.CategoryTheory.PseudofunctorPointFiber

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {U T : C} {ξ ξ' : F.obj (.mk (op U))}
  (e : ξ ≅ ξ') (η : F.obj (.mk (op T)))

/-- Change the atlas object using the pulled-back actual isomorphism. -/
def mapPoints (Z : Over T) : Points F ξ η Z → Points F ξ' η Z :=
  fun x ↦ ⟨x.1, (F.map x.1.op.toLoc).toFunctor.mapIso e.symm ≪≫ x.2⟩

/-- Changing the atlas object commutes with coherent restriction. -/
lemma mapPoints_restrict {Z Z' : Over T} (q : Z' ⟶ Z) (x : Points F ξ η Z) :
    mapPoints F e η Z' (restrict F ξ η q x) =
      restrict F ξ' η q (mapPoints F e η Z x) := by
  rcases x with ⟨a, d⟩
  dsimp only [mapPoints, restrict]
  congr 1
  apply Iso.ext
  simp only [pullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
  have hn := (Cat.Hom.toNatIso (F.mapComp' a.op.toLoc q.left.op.toLoc
    (q.left ≫ a).op.toLoc (by simp))).hom.naturality e.inv
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hn
  rw [reassoc_of% hn]

/-- The inverse change uses the inverse actual isomorphism. -/
lemma mapPoints_symm (Z : Over T) (x : Points F ξ η Z) :
    mapPoints F e.symm η Z (mapPoints F e η Z x) = x := by
  rcases x with ⟨a, d⟩
  simp [mapPoints]

/-- The equivalence preserves every actual map to the atlas scheme. -/
def pointsEquiv (Z : Over T) : Points F ξ η Z ≃ Points F ξ' η Z where
  toFun := mapPoints F e η Z
  invFun := mapPoints F e.symm η Z
  left_inv := mapPoints_symm F e η Z
  right_inv := mapPoints_symm F e.symm η Z

/-- Isomorphic atlas objects have naturally isomorphic full point fibres. -/
def presheafIso : presheaf F ξ η ≅ presheaf F ξ' η :=
  NatIso.ofComponents (fun Z ↦ (pointsEquiv F e η Z.unop).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact mapPoints_restrict F e η q.unop x)

end Langlands.CategoryTheory.PseudofunctorPointFiberObjectIso

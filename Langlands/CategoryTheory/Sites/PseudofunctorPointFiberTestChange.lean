import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber

/-! # Point fibres after changing the test object -/

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CategoryTheory.PseudofunctorPointFiberTestChange

open Langlands.CategoryTheory.PseudofunctorPointFiber
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C]
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {U T : C} (ξ : F.obj (.mk (op U)))

section ObjectIso

variable {η η' : F.obj (.mk (op T))} (e : η ≅ η')

/-- Change the test object using the pulled-back actual isomorphism. -/
def isoMapPoints (Z : Over T) : Points F ξ η Z → Points F ξ η' Z :=
  fun x ↦ ⟨x.1, x.2 ≪≫ (F.map Z.hom.op.toLoc).toFunctor.mapIso e⟩

/-- Changing the test object commutes with coherent restriction. -/
lemma isoMapPoints_restrict {Z Z' : Over T} (q : Z' ⟶ Z) (x : Points F ξ η Z) :
    isoMapPoints F ξ e Z' (restrict F ξ η q x) =
      restrict F ξ η' q (isoMapPoints F ξ e Z x) := by
  rcases x with ⟨a, d⟩
  dsimp only [isoMapPoints, restrict]
  congr 1
  apply Iso.ext
  simp only [pullIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv]
  have hn := (Cat.Hom.toNatIso (F.mapComp' Z.hom.op.toLoc q.left.op.toLoc
    Z'.hom.op.toLoc (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w q]))).inv.naturality
      e.hom
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hn
  rw [hn]

/-- The inverse change uses the inverse actual isomorphism. -/
lemma isoMapPoints_symm (Z : Over T) (x : Points F ξ η Z) :
    isoMapPoints F ξ e.symm Z (isoMapPoints F ξ e Z x) = x := by
  rcases x with ⟨a, d⟩
  simp [isoMapPoints]

/-- Isomorphic test objects have equivalent actual point types. -/
def isoPointsEquiv (Z : Over T) : Points F ξ η Z ≃ Points F ξ η' Z where
  toFun := isoMapPoints F ξ e Z
  invFun := isoMapPoints F ξ e.symm Z
  left_inv := isoMapPoints_symm F ξ e Z
  right_inv := isoMapPoints_symm F ξ e.symm Z

/-- Isomorphic test objects have naturally isomorphic full point fibres. -/
def isoPresheafIso : presheaf F ξ η ≅ presheaf F ξ η' :=
  NatIso.ofComponents (fun Z ↦ (isoPointsEquiv F ξ e Z.unop).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact isoMapPoints_restrict F ξ e q.unop x)

end ObjectIso

section BaseChange

variable (η : F.obj (.mk (op T))) {T' : C} (g : T' ⟶ T)

/-- The composition comparison from a pullback of the pulled-back test object. -/
def compIso (Z : Over T') :
    (F.map Z.hom.op.toLoc).toFunctor.obj ((F.map g.op.toLoc).toFunctor.obj η) ≅
      (F.map ((Over.map g).obj Z).hom.op.toLoc).toFunctor.obj η :=
  ((Cat.Hom.toNatIso (F.mapComp' g.op.toLoc Z.hom.op.toLoc
    ((Over.map g).obj Z).hom.op.toLoc rfl)).app η).symm

/-- Points over the pulled-back test object are points over the composite test map. -/
def basePointsEquiv (Z : Over T') :
    Points F ξ ((F.map g.op.toLoc).toFunctor.obj η) Z ≃
      Points F ξ η ((Over.map g).obj Z) where
  toFun x := ⟨x.1, x.2 ≪≫ compIso F η g Z⟩
  invFun x := ⟨x.1, x.2 ≪≫ (compIso F η g Z).symm⟩
  left_inv x := by
    rcases x with ⟨a, d⟩
    simp
  right_inv x := by
    rcases x with ⟨a, d⟩
    simp

/-- The base map of a point is unchanged by the base-change equivalence. -/
@[simp]
lemma basePointsEquiv_fst (Z : Over T')
    (x : Points F ξ ((F.map g.op.toLoc).toFunctor.obj η) Z) :
    (basePointsEquiv F ξ η g Z x).1 = x.1 := rfl

/-- Changing the test object along `g` commutes with coherent restriction. -/
lemma basePointsEquiv_restrict {Z Z' : Over T'} (q : Z' ⟶ Z)
    (x : Points F ξ ((F.map g.op.toLoc).toFunctor.obj η) Z) :
    basePointsEquiv F ξ η g Z' (restrict F ξ _ q x) =
      restrict F ξ η ((Over.map g).map q) (basePointsEquiv F ξ η g Z x) := by
  rcases x with ⟨a, d⟩
  dsimp only [basePointsEquiv, restrict, Equiv.coe_fn_mk, Over.map_map_left]
  congr 1
  apply Iso.ext
  simp only [pullIso_hom, pullHom, compIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Cat.Hom.toNatIso_inv, Functor.map_comp, Category.assoc]
  rw [Pseudofunctor.whiskerLeft_mapComp'_inv_comp_mapComp'₀₁₃_inv_app F g.op.toLoc
    Z.hom.op.toLoc q.left.op.toLoc ((Over.map g).obj Z).hom.op.toLoc Z'.hom.op.toLoc
    ((Over.map g).obj Z').hom.op.toLoc rfl
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, Over.w q]) rfl η]

/-- Pulling back the test object along `g` restricts the full point fibre along
`Over.map g`, with its coherent restriction maps. -/
def basePresheafIso :
    presheaf F ξ ((F.map g.op.toLoc).toFunctor.obj η) ≅ (Over.map g).op ⋙ presheaf F ξ η :=
  NatIso.ofComponents (fun Z ↦ (basePointsEquiv F ξ η g Z.unop).toIso) (by
    intro Z Z' q
    apply ConcreteCategory.hom_ext
    intro x
    exact basePointsEquiv_restrict F ξ η g q.unop x)

end BaseChange

end Langlands.CategoryTheory.PseudofunctorPointFiberTestChange

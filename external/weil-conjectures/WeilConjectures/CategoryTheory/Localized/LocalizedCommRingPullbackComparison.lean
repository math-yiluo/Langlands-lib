/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.Localized.LocalizedSetPullbackComparison

/-! # The canonical commutative-ring comparison for localization of a site

Source: Stacks Project, Sites, Tag 03CF; Modules on Sites, Tag 04J0.
(blueprint: lem-weil-pbc-slice-commRing-pullback-isIso).
-/

@[expose] public noncomputable section

set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
namespace CategoryTheory

/-- Transport the section formulas along equality of internal rings.
Source: Stacks Tag 00YR, rings as sextuples. Eliminate the equality of rings;
proof irrelevance identifies the two carrier equalities, so the formulas agree. -/
private theorem transportRingSectionOperations.{v, w} {C : Type v} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget CommRingCat.{w})]
    (A : Sheaf J CommRingCat.{w}) (Y X : CommRingObjCat (Sheaf J (Type w)))
    (p : Y = X) (h : Y.X = (sheafForget J).obj A)
    (k : (sheafForget J).obj A = X.X) (Z : Cᵒᵖ)
    (ops :
      (∀ a b, (eqToHom h).hom.app Z
        ((AddMonObj.add (X := Y.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom h).hom.app Z a) +
            (show A.obj.obj Z from (eqToHom h).hom.app Z b)) ∧
      (∀ t, (eqToHom h).hom.app Z ((AddMonObj.zero (X := Y.X)).hom.app Z t) =
        (0 : A.obj.obj Z)) ∧
      (∀ a b, (eqToHom h).hom.app Z ((MonObj.mul (X := Y.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom h).hom.app Z a) *
            (show A.obj.obj Z from (eqToHom h).hom.app Z b)) ∧
      (∀ t, (eqToHom h).hom.app Z ((MonObj.one (X := Y.X)).hom.app Z t) =
        (1 : A.obj.obj Z))) :
      (∀ a b, (eqToHom k.symm).hom.app Z
        ((AddMonObj.add (X := X.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom k.symm).hom.app Z a) +
            (show A.obj.obj Z from (eqToHom k.symm).hom.app Z b)) ∧
      (∀ t, (eqToHom k.symm).hom.app Z ((AddMonObj.zero (X := X.X)).hom.app Z t) =
        (0 : A.obj.obj Z)) ∧
      (∀ a b, (eqToHom k.symm).hom.app Z ((MonObj.mul (X := X.X)).hom.app Z (a, b)) =
          (show A.obj.obj Z from (eqToHom k.symm).hom.app Z a) *
            (show A.obj.obj Z from (eqToHom k.symm).hom.app Z b)) ∧
      (∀ t, (eqToHom k.symm).hom.app Z ((MonObj.one (X := X.X)).hom.app Z t) =
        (1 : A.obj.obj Z)) := by
  cases p
  exact ops

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def ringAdd.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) :
    (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Add.add (G.obj.obj W) inferInstance
       ((prod.fst : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W)
       ((prod.snd : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       have hf := ConcreteCategory.congr_hom ((prod.fst : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       have hs := ConcreteCategory.congr_hom ((prod.snd : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       dsimp at hf hs ⊢
       rw [hf, hs]
       exact (G.obj.map f).hom.map_add _ _ |>.symm }⟩
private noncomputable def ringMul.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) :
    (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun x ↦ @Mul.mul (G.obj.obj W) inferInstance
       ((prod.fst : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W)
       ((prod.snd : (sheafForget J |>.obj G) ⨯ (sheafForget J |>.obj G) ⟶
         (sheafForget J |>.obj G)).hom.app W x : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       have hf := ConcreteCategory.congr_hom ((prod.fst : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       have hs := ConcreteCategory.congr_hom ((prod.snd : (sheafForget J |>.obj G) ⨯
         (sheafForget J |>.obj G) ⟶ (sheafForget J |>.obj G)).hom.naturality f) x
       dsimp at hf hs ⊢
       rw [hf, hs]
       exact (G.obj.map f).hom.map_mul _ _ |>.symm }⟩
private noncomputable def ringZero.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) : ⊤_ (Sheaf J (Type w)) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (0 : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       exact (G.obj.map f).hom.map_zero |>.symm }⟩
private noncomputable def ringOne.{uC, vC, w} {C : Type uC} [Category.{vC} C]
    (J : GrothendieckTopology C) [J.HasSheafCompose (forget CommRingCat.{w})]
    (G : Sheaf J CommRingCat.{w}) : ⊤_ (Sheaf J (Type w)) ⟶ (sheafForget J |>.obj G) :=
  ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : G.obj.obj W))
     naturality := by
       intro W W' f
       ext x
       exact (G.obj.map f).hom.map_one |>.symm }⟩

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J] (V : D)
  [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]

end CategoryTheory

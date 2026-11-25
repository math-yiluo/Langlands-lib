/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.RoosFinitePrefixes

/-!
# Limits of finite-prefix towers

Source: Stacks Project, Tag 07KW, proof of Lemma 15.88.1.
(blueprint: lem-pc-roos-finite-prefix-limits).
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- Evaluation on a finite prefix. 
(blueprint: lem-pc-roos-finite-prefix-limits)
-/
def roosPrefixEval (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (n i : ℕ)
    (h : i < n + s) : (roosPrefixTower s A).obj (Opposite.op n) ⟶
      A.obj (Opposite.op i) :=
  AddCommGrpCat.ofHom
    { toFun := fun x ↦ x ⟨i, h⟩
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- Restriction of an infinite tuple to a finite prefix. 
(blueprint: lem-pc-roos-finite-prefix-limits)
-/
noncomputable def roosPrefixCone (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    Cone (roosPrefixTower s A) where
  pt := ∏ᶜ fun i : ℕ ↦ A.obj (Opposite.op i)
  π :=
    { app := fun n ↦ AddCommGrpCat.ofHom
        { toFun := fun x i ↦ Pi.π (fun i : ℕ ↦ A.obj (Opposite.op i)) i.val x
          map_zero' := by ext i; exact map_zero _
          map_add' := by intros; ext i; exact map_add _ _ _ }
      naturality := by intros; rfl }

/-- (blueprint: lem-pc-roos-finite-prefix-limits) -/
theorem roosPrefixCone_coordinate (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (c : Cone (roosPrefixTower s A)) (n m i : ℕ) (hn : i < n + s) (hm : i < m + s) :
    c.π.app (Opposite.op n) ≫ roosPrefixEval s A n i hn =
      c.π.app (Opposite.op m) ≫ roosPrefixEval s A m i hm := by
  have h₁ := congrArg (fun f ↦ f ≫ roosPrefixEval s A n i hn)
    (c.w (homOfLE (Nat.le_max_left n m)).op)
  have h₂ := congrArg (fun f ↦ f ≫ roosPrefixEval s A m i hm)
    (c.w (homOfLE (Nat.le_max_right n m)).op)
  exact h₁.symm.trans h₂

/-- Compatible finite prefixes are exactly infinite tuples.

Source: Stacks Project, Tag 07KW, proof of Lemma 15.88.1.
(blueprint: lem-pc-roos-finite-prefix-limits).

Extract coordinate i from prefix i+1. Compatibility makes this the same as its
value in any prefix containing i: compare both with the prefix of maximum length.
These extractions define the unique map to the product; conversely restriction
of a tuple gives compatible prefixes. The argument includes the empty prefix. -/
noncomputable def roosPrefixConeIsLimit (s : ℕ) (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsLimit (roosPrefixCone s A) where
  lift c := Pi.lift (fun i ↦ c.π.app (Opposite.op (i + 1)) ≫
    roosPrefixEval s A (i + 1) i (by omega))
  fac c n := by
    ext x
    funext i
    change ((Pi.lift _ : c.pt ⟶ (roosPrefixCone s A).pt) ≫
      Pi.π (fun j : ℕ ↦ A.obj (Opposite.op j)) i.val) x = _
    rw [Pi.lift_comp_π]
    exact ConcreteCategory.congr_hom
      (roosPrefixCone_coordinate s A c (i.val + 1) n.unop i.val (by omega) i.isLt) x
  uniq c m hm := by
    apply Pi.hom_ext
    intro i
    rw [Pi.lift_comp_π]
    have h := congrArg (fun f ↦ f ≫
      roosPrefixEval s A (i + 1) i (by omega)) (hm (Opposite.op (i + 1)))
    exact h

end CategoryTheory

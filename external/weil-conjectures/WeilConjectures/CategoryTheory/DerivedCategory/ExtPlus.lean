/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# `Ext` as morphisms in the bounded below derived category

For objects `A` and `N` of an abelian category `C`, maps `A[0] ⟶ N[0]⟦n⟧` in `D⁺(C)` are the
`Ext`-groups `Extⁿ(A, N)` for `n ≥ 0`, and vanish for `n < 0`.

## Main definitions

- `DerivedCategory.Plus.shiftedHomAddEquivExt`: `Hom(A[0], N[0]⟦n⟧) ≃+ Extⁿ(A, N)`.

## Main statements

- `DerivedCategory.Plus.subsingleton_shiftedHom_of_neg`: `Hom(A[0], N[0]⟦q⟧) = 0` for `q < 0`.
-/

@[expose] public section

universe w w' v u

open CategoryTheory Limits Opposite Abelian

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w'} C]

/-- The comparison of maps `A[0] ⟶ N[0]⟦q⟧` in `D⁺(C)` with maps in `D(C)`. -/
noncomputable def shiftedHomEquiv (A N : C) (q : ℤ) :
    ((singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) ≃
      ((DerivedCategory.singleFunctor C 0).obj A ⟶
        ((DerivedCategory.singleFunctor C 0).obj N)⟦q⟧) :=
  ((ObjectProperty.fullyFaithfulι _).homEquiv).trans
    (((singleFunctorιIso C 0).app A).homCongr ((Plus.ι.commShiftIso q).app _ ≪≫
      (shiftFunctor _ q).mapIso ((singleFunctorιIso C 0).app N)))

lemma shiftedHomEquiv_apply (A N : C) (q : ℤ)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) :
    shiftedHomEquiv A N q f = ((singleFunctorιIso C 0).app A).inv ≫ Plus.ι.map f ≫
      (Plus.ι.commShiftIso q).hom.app _ ≫
        (shiftFunctor _ q).map ((singleFunctorιIso C 0).hom.app N) := by
  rfl

lemma shiftedHomEquiv_add (A N : C) (q : ℤ)
    (f g : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) :
    shiftedHomEquiv A N q (f + g) = shiftedHomEquiv A N q f + shiftedHomEquiv A N q g := by
  simp only [shiftedHomEquiv_apply, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add]

lemma shiftedHomEquiv_comp (A : C) {N N' : C} (q : ℤ)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) (g : N ⟶ N') :
    shiftedHomEquiv A N' q (f ≫ (shiftFunctor _ q).map ((singleFunctor C 0).map g)) =
      shiftedHomEquiv A N q f ≫
        (shiftFunctor _ q).map ((DerivedCategory.singleFunctor C 0).map g) := by
  simp only [shiftedHomEquiv_apply, Functor.map_comp, Category.assoc]
  congr 2
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  exact (singleFunctorιIso C 0).hom.naturality g

lemma shiftedHomEquiv_precomp {A A' : C} (N : C) (q : ℤ) (g : A' ⟶ A)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) :
    shiftedHomEquiv A' N q ((singleFunctor C 0).map g ≫ f) =
      (DerivedCategory.singleFunctor C 0).map g ≫ shiftedHomEquiv A N q f := by
  simp only [shiftedHomEquiv_apply, Functor.map_comp, Category.assoc]
  rw [Iso.app_inv, Iso.app_inv]
  exact ((singleFunctorιIso C 0).inv.naturality_assoc g _).symm

/-- Maps `A[0] ⟶ N[0]⟦q⟧` in `D⁺(C)` vanish for `q < 0`. -/
lemma subsingleton_shiftedHom_of_neg (A N : C) (q : ℤ) (hq : q < 0) :
    Subsingleton ((singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦q⟧) := by
  have : DerivedCategory.TStructure.t.IsGE (((DerivedCategory.singleFunctor C 0).obj N)⟦q⟧) (-q) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 q (-q)
  refine ⟨fun f g ↦ (shiftedHomEquiv A N q).injective ?_⟩
  rw [DerivedCategory.TStructure.t.zero (shiftedHomEquiv A N q f) 0 (-q),
    DerivedCategory.TStructure.t.zero (shiftedHomEquiv A N q g) 0 (-q)]

variable [HasExt.{w} C]

/-- Maps `A[0] ⟶ N[0]⟦n⟧` in `D⁺(C)` are the `Ext`-group `Extⁿ(A, N)`. -/
noncomputable def shiftedHomAddEquivExt (A N : C) (n : ℕ) :
    ((singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦(n : ℤ)⟧) ≃+ Ext.{w} A N n :=
  AddEquiv.trans
    { toEquiv := shiftedHomEquiv A N n
      map_add' := shiftedHomEquiv_add A N n }
    Ext.homAddEquiv.symm

lemma shiftedHomAddEquivExt_comp (A : C) {N N' : C} (n : ℕ)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦(n : ℤ)⟧) (g : N ⟶ N') :
    shiftedHomAddEquivExt A N' n (f ≫ (shiftFunctor _ (n : ℤ)).map ((singleFunctor C 0).map g)) =
      (shiftedHomAddEquivExt A N n f).comp (Ext.mk₀ g) (add_zero n) := by
  have key {N : C} (x : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj A)
      ((DerivedCategory.singleFunctor C 0).obj N) (n : ℤ)) :
      (Ext.homAddEquiv.symm x : Ext.{w} A N n).hom = x :=
    Ext.homAddEquiv.apply_symm_apply x
  refine (Ext.homAddEquiv (X := A) (Y := N') (n := n)).injective ?_
  rw [Ext.homAddEquiv_apply, Ext.homAddEquiv_apply, ← Ext.hom_comp_singleFunctor_map_shift]
  simp only [shiftedHomAddEquivExt, AddEquiv.trans_apply, AddEquiv.coe_mk]
  rw [key, key]
  exact shiftedHomEquiv_comp A n f g

lemma shiftedHomAddEquivExt_precomp {A A' : C} (N : C) (n : ℕ) (g : A' ⟶ A)
    (f : (singleFunctor C 0).obj A ⟶ ((singleFunctor C 0).obj N)⟦(n : ℤ)⟧) :
    shiftedHomAddEquivExt A' N n ((singleFunctor C 0).map g ≫ f) =
      (Ext.mk₀ g).comp (shiftedHomAddEquivExt A N n f) (zero_add n) := by
  have key {A : C} (x : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj A)
      ((DerivedCategory.singleFunctor C 0).obj N) (n : ℤ)) :
      (Ext.homAddEquiv.symm x : Ext.{w} A N n).hom = x :=
    Ext.homAddEquiv.apply_symm_apply x
  refine (Ext.homAddEquiv (X := A') (Y := N) (n := n)).injective ?_
  rw [Ext.homAddEquiv_apply, Ext.homAddEquiv_apply, Ext.comp_hom, Ext.mk₀_hom]
  simp only [shiftedHomAddEquivExt, AddEquiv.trans_apply, AddEquiv.coe_mk]
  rw [key, key, ShiftedHom.mk₀_comp]
  exact shiftedHomEquiv_precomp N n g f

end DerivedCategory.Plus

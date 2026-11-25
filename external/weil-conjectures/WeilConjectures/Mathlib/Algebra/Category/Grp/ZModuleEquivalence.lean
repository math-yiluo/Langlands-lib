/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Ring.ULift

/-!
# Abelian groups as `ℤ`-modules

The functor `AddCommGrpCat.toModuleCatInt : AddCommGrpCat ⥤ ModuleCat ℤ` regards an abelian group
as a `ℤ`-module. It is right adjoint to the forgetful functor
(`ModuleCat.forget₂AddCommGrpToModuleCatIntAdj`).
-/

@[expose] public section

universe u

open CategoryTheory

/-- An abelian group regarded as a `ℤ`-module. -/
@[simps]
def AddCommGrpCat.toModuleCatInt : AddCommGrpCat.{u} ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

/-- The forgetful functor from `ℤ`-modules to abelian groups is left adjoint to regarding an
abelian group as a `ℤ`-module. -/
def ModuleCat.forget₂AddCommGrpToModuleCatIntAdj :
    forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u} ⊣ AddCommGrpCat.toModuleCatInt :=
  Adjunction.mkOfHomEquiv
    { homEquiv M A :=
        { toFun f := ModuleCat.ofHom
            { toFun := f
              map_add' := map_add f.hom
              map_smul' n x := by
                convert! map_zsmul f.hom n x
                ext
                apply int_smul_eq_zsmul }
          invFun g := AddCommGrpCat.ofHom g.hom.toAddMonoidHom
          left_inv _ := rfl
          right_inv _ := rfl }
      homEquiv_naturality_left_symm _ _ := rfl
      homEquiv_naturality_right _ _ := rfl }

namespace ModuleCat

universe v w

/-- A scalar `r : ULift ℤ` acts on a `ULift ℤ`-module as the integer `r.down`. -/
lemma uliftInt_smul_eq_zsmul {M : Type*} [AddCommGroup M] [Module (ULift.{w} ℤ) M]
    (r : ULift.{w} ℤ) (x : M) : r • x = r.down • x := by
  rw [← Int.cast_smul_eq_zsmul (ULift.{w} ℤ)]
  rfl

/-- The forgetful functor from `ULift ℤ`-modules to abelian groups is full. -/
instance forget₂_uliftInt_full :
    (forget₂ (ModuleCat.{v} (ULift.{w} ℤ)) AddCommGrpCat.{v}).Full where
  map_surjective {A B} f :=
    ⟨ModuleCat.ofHom
      { toFun := f
        map_add' := map_add f.hom
        map_smul' r x := by
          rw [uliftInt_smul_eq_zsmul, uliftInt_smul_eq_zsmul]
          exact map_zsmul f.hom r.down x }, rfl⟩

/-- The forgetful functor from `ULift ℤ`-modules to abelian groups is essentially surjective:
an abelian group is a `ULift ℤ`-module through `ULift ℤ ≃+* ℤ`. -/
instance forget₂_uliftInt_essSurj :
    (forget₂ (ModuleCat.{v} (ULift.{w} ℤ)) AddCommGrpCat.{v}).EssSurj where
  mem_essImage A :=
    letI : Module (ULift.{w} ℤ) A := Module.compHom A ULift.ringEquiv.toRingHom
    ⟨ModuleCat.of (ULift.{w} ℤ) A, ⟨{ hom := 𝟙 A, inv := 𝟙 A }⟩⟩

/-- The forgetful functor from `ULift ℤ`-modules to abelian groups is an equivalence. -/
instance forget₂_uliftInt_isEquivalence :
    (forget₂ (ModuleCat.{v} (ULift.{w} ℤ)) AddCommGrpCat.{v}).IsEquivalence where

end ModuleCat

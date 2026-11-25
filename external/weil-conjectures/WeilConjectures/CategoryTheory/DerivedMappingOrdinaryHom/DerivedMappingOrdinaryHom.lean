/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.ULift

/-! # Ordinary linear Hom complexes in independent coefficient universes

Source: Stacks Project, Differential Graded Algebra, Example 09L9.
The differential is Mathlib's Hom differential and the maps are pre/postcomposition.
(blueprint: lem-sf-derived-mapping-ordinary-hom)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe b v u

open CategoryTheory CochainComplex.HomComplex Opposite

namespace CategoryTheory.DerivedMappingOrdinaryHom

variable (B : Type b) [CommRing B]
  {A : Type u} [Category.{v} A] [Preadditive A] [Linear B A]

/-- The scalar-linear Hom differential, with its carrier lifted once.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-hom). -/
def differential (X Y : CochainComplex A ℤ) (n m : ℤ) :
    ULift.{b} (Cochain X Y n) →ₗ[ULift.{v} B] ULift.{b} (Cochain X Y m) where
  toFun x := ULift.up (δ n m x.down)
  map_add' x y := congrArg ULift.up ((δ_hom B X Y n m).map_add x.down y.down)
  map_smul' a x := congrArg ULift.up ((δ_hom B X Y n m).map_smul a.down x.down)

/-- The actual product Hom complex, with the prescribed signed differential.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-hom). -/
def complex (X Y : CochainComplex A ℤ) : CochainComplex (ModuleCat.{max b v} (ULift.{v} B)) ℤ
    where
  X n := ModuleCat.of (ULift.{v} B) (ULift.{b} (Cochain X Y n))
  d n m := ModuleCat.ofHom (differential B X Y n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg ULift.up (δ_shape n m h x.down)
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg ULift.up (δ_δ n m k x.down)

/-- Precomposition and postcomposition on every homogeneous cochain.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-hom). -/
def mapTerm {X X' Y Y' : CochainComplex A ℤ}
    (f : X' ⟶ X) (g : Y ⟶ Y') (n : ℤ) :
    (complex B X Y).X n ⟶ (complex B X' Y').X n :=
  ModuleCat.ofHom
    { toFun := fun x ↦ ULift.up
        ((Cochain.ofHom f).comp (x.down.comp (Cochain.ofHom g) (add_zero n)) (zero_add n))
      map_add' := by intros; apply ULift.ext; simp
      map_smul' := by intros; apply ULift.ext; simp }

/-- Actual chain map of product Hom complexes.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-hom). -/
def map {X X' Y Y' : CochainComplex A ℤ} (f : X' ⟶ X) (g : Y ⟶ Y') :
    complex B X Y ⟶ complex B X' Y' where
  f n := mapTerm B f g n
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    change δ n m ((Cochain.ofHom f).comp
      (x.down.comp (Cochain.ofHom g) (add_zero n)) (zero_add n)) =
        (Cochain.ofHom f).comp ((δ n m x.down).comp (Cochain.ofHom g) (add_zero m))
          (zero_add m)
    rw [δ_ofHom_comp, δ_comp_ofHom]

/-- The linear Hom complex is a genuine bifunctor on unbounded complexes.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-hom). -/
def functor : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ ⥤
    CochainComplex (ModuleCat.{max b v} (ULift.{v} B)) ℤ where
  obj X := complex B X.1.unop X.2
  map f := map B f.1.unop f.2
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    change (Cochain.ofHom (𝟙 X.1.unop)).comp
      (x.down.comp (Cochain.ofHom (𝟙 X.2)) (add_zero n)) (zero_add n) = x.down
    simp
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    change (Cochain.ofHom (g.1.unop ≫ f.1.unop)).comp
      (x.down.comp (Cochain.ofHom (f.2 ≫ g.2)) (add_zero n)) (zero_add n) =
        (Cochain.ofHom g.1.unop).comp
          (((Cochain.ofHom f.1.unop).comp
            (x.down.comp (Cochain.ofHom f.2) (add_zero n)) (zero_add n)).comp
              (Cochain.ofHom g.2) (add_zero n)) (zero_add n)
    ext p q hpq
    simp

/-- The bifunctor acts by the actual componentwise pre/postcomposition formula.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-hom).
Proof: evaluate the two zero-degree cochains and use the definition of composition. -/
theorem map_apply (X X' Y Y' : CochainComplex A ℤ) (f : X' ⟶ X) (g : Y ⟶ Y')
    (n p q : ℤ) (hpq : p + n = q) (x : ((functor B).obj (op X, Y)).X n) :
    ((((functor B).map (X := (op X, Y)) (Y := (op X', Y')) (f.op, g)).f n x).down).v p q hpq =
      f.f p ≫ x.down.v p q hpq ≫ g.f q := by
  change ((Cochain.ofHom f).comp
    (x.down.comp (Cochain.ofHom g) (add_zero n)) (zero_add n)).v p q hpq = _
  simp

end CategoryTheory.DerivedMappingOrdinaryHom

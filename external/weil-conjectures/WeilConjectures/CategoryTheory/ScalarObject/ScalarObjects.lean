/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Algebra.Ring.Equiv

/-! # Scalar actions in preadditive categories

Source: Stacks Project, Tag 04JQ, transport of scalar operations across an additive
fully faithful equivalence. (blueprint: lem-exc-scalar-objects-equivalence)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe r v v' u u'

open CategoryTheory

namespace CategoryTheory

/-- An object equipped with a ring action by endomorphisms.
Source: Stacks Project, Tag 04JQ, scalar enhancement of abelian objects.
(blueprint: lem-exc-scalar-objects-equivalence) -/
structure ScalarObject (R : Type r) [Ring R] (C : Type u) [Category.{v} C]
    [Preadditive C] where
  X : C
  ρ : R →+* End X

namespace ScalarObject

variable {R : Type r} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

/-- Scalar-compatible maps. Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-objects-equivalence) -/
structure Hom (M N : ScalarObject R C) where
  hom : M.X ⟶ N.X
  comm : ∀ a : R, (M.ρ a).asHom ≫ hom = hom ≫ (N.ρ a).asHom

@[ext] theorem hom_ext {M N : ScalarObject R C} {f g : Hom M N}
    (h : f.hom = g.hom) : f = g := by cases f; cases g; cases h; rfl

instance : Category (ScalarObject R C) where
  Hom := Hom
  id M := ⟨𝟙 M.X, fun _ ↦ by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, fun a ↦ by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, Category.assoc]⟩
  id_comp f := hom_ext (Category.id_comp _)
  comp_id f := hom_ext (Category.comp_id _)
  assoc f g h := hom_ext (Category.assoc _ _ _)

/-- Forget scalar operations. Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-objects-equivalence) -/
def forget (R : Type r) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C] :
    ScalarObject R C ⥤ C where
  obj M := M.X
  map f := f.hom

instance : (forget R C).Faithful where
  map_injective h := hom_ext h

/-- An additive functor acts on endomorphism rings.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-objects-equivalence) -/
def mapEndRing (F : C ⥤ D) [F.Additive] (X : C) : End X →+* End (F.obj X) where
  toFun a := .of (F.map a.asHom)
  map_one' := End.ext (F.map_id X)
  map_mul' a b := End.ext (F.map_comp b.asHom a.asHom)
  map_zero' := End.ext (F.map_zero X X)
  map_add' _a _b := End.ext F.map_add

/-- Transport scalar operations by an additive functor.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-objects-equivalence) -/
def map (F : C ⥤ D) [F.Additive] : ScalarObject R C ⥤ ScalarObject R D where
  obj M := ⟨F.obj M.X, (mapEndRing F M.X).comp M.ρ⟩
  map f := ⟨F.map f.hom, fun a ↦ by
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← F.map_comp, f.comm, F.map_comp]⟩
  map_id M := hom_ext (F.map_id M.X)
  map_comp f g := hom_ext (F.map_comp f.hom g.hom)

/-- Full faithfulness transports scalar-compatible maps.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-objects-equivalence) -/
noncomputable def mapFullyFaithful (F : C ⥤ D) [F.Additive]
    (hF : F.FullyFaithful) : (map (R := R) F).FullyFaithful where
  preimage {M N} f := ⟨hF.preimage f.hom, fun a ↦ hF.map_injective (by
    simp only [F.map_comp, hF.map_preimage]
    exact f.comm a)⟩
  map_preimage f := hom_ext (hF.map_preimage f.hom)
  preimage_map f := hom_ext (hF.preimage_map f.hom)

/-- Conjugate a ring action along an isomorphism.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-objects-equivalence) -/
def conjugate (X Y : D) (i : X ≅ Y) : End Y →+* End X where
  toFun a := .of (i.hom ≫ a.asHom ≫ i.inv)
  map_one' := by
    apply End.ext
    simp
  map_mul' a b := by
    apply End.ext
    change i.hom ≫ (b.asHom ≫ a.asHom) ≫ i.inv =
      (i.hom ≫ b.asHom ≫ i.inv) ≫ (i.hom ≫ a.asHom ≫ i.inv)
    simp [Category.assoc]
  map_zero' := by
    apply End.ext
    simp
  map_add' a b := by
    apply End.ext
    change i.hom ≫ (a.asHom + b.asHom) ≫ i.inv =
      (i.hom ≫ a.asHom ≫ i.inv) + (i.hom ≫ b.asHom ≫ i.inv)
    simp only [Preadditive.comp_add, Preadditive.add_comp]

/-- Scalar operations lift uniquely through a fully faithful additive functor.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-objects-equivalence) -/
noncomputable def endRingEquiv (F : C ⥤ D) [F.Additive]
    (hF : F.FullyFaithful) (X : C) : End X ≃+* End (F.obj X) :=
  RingEquiv.ofBijective (mapEndRing F X) (hF.mulEquivEnd X).bijective

/-- An additive equivalence induces an equivalence of scalar objects, with precisely
its original underlying functor. Full faithfulness lifts compatible maps. For essential
surjectivity, conjugate an action by the counit and pull it back through the isomorphism
of endomorphism rings; the counit then becomes a scalar-compatible isomorphism.
Source: Stacks Project, Tag 04JQ, scalar enhancement.
(blueprint: lem-exc-scalar-objects-equivalence) -/
noncomputable def equivalence (e : C ≌ D) [e.functor.Additive] :
    ScalarObject R C ≌ ScalarObject R D := by
  let F := map (R := R) e.functor
  let ff := mapFullyFaithful (R := R) e.functor e.fullyFaithfulFunctor
  have : F.Full := ff.full
  have : F.Faithful := ff.faithful
  have : F.EssSurj := by
    constructor
    intro N
    let X := e.inverse.obj N.X
    let i := e.counitIso.app N.X
    let ρ : R →+* End X :=
      ((endRingEquiv e.functor e.fullyFaithfulFunctor X).symm.toRingHom).comp
        ((conjugate _ _ i).comp N.ρ)
    let M : ScalarObject R C := ⟨X, ρ⟩
    have hρ (a : R) : e.functor.map (ρ a).asHom = i.hom ≫ (N.ρ a).asHom ≫ i.inv :=
      congrArg End.asHom
        ((endRingEquiv e.functor e.fullyFaithfulFunctor X).apply_symm_apply _)
    refine ⟨M, ⟨{
      hom := ⟨i.hom, ?_⟩
      inv := ⟨i.inv, ?_⟩
      hom_inv_id := hom_ext i.hom_inv_id
      inv_hom_id := hom_ext i.inv_hom_id }⟩⟩
    · intro a
      change e.functor.map (ρ a).asHom ≫ i.hom = i.hom ≫ (N.ρ a).asHom
      rw [hρ]
      simp [Category.assoc]
    · intro a
      change (N.ρ a).asHom ≫ i.inv = i.inv ≫ e.functor.map (ρ a).asHom
      rw [hρ]
      simp [← Category.assoc]
  have : F.IsEquivalence := {}
  exact F.asEquivalence

end ScalarObject
end CategoryTheory

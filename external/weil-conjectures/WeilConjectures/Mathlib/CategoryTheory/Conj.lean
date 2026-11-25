/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Conjugation in preadditive categories

In a preadditive category, conjugation by an isomorphism `X ≅ Y` is a ring isomorphism
`End X ≃+* End Y` (`CategoryTheory.Iso.conjRingEquiv`), and an additive functor induces a ring
homomorphism `End X →+* End (F.obj X)` (`CategoryTheory.Functor.mapEndRingHom`).
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- Conjugation by an isomorphism `α : X ≅ Y`, as a ring isomorphism `End X ≃+* End Y`. -/
def Iso.conjRingEquiv {X Y : C} (α : X ≅ Y) : End X ≃+* End Y where
  __ := α.conj
  map_add' f g := End.ext (by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, MulEquiv.coe_toEquiv,
      Iso.conj_apply_asHom, End.add_asHom, Preadditive.add_comp, Preadditive.comp_add])

@[simp]
lemma Iso.conjRingEquiv_apply {X Y : C} (α : X ≅ Y) (f : End X) :
    α.conjRingEquiv f = .of (α.inv ≫ (f).asHom ≫ α.hom) :=
  rfl

/-- An additive functor induces a ring homomorphism `End X →+* End (F.obj X)`. -/
@[simps!]
def Functor.mapEndRingHom (F : C ⥤ D) [F.Additive] (X : C) : End X →+* End (F.obj X) where
  __ := F.mapEnd X
  map_zero' := End.ext (F.map_zero X X)
  map_add' _ _ := End.ext F.map_add

end CategoryTheory

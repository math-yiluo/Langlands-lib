/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence

/-! # Twisting the transitions of an abelian tower by a fixed power

The underlying object at each level is unchanged. Only the transition maps acquire a
factor of l. This is the degree -1 term of the simultaneous coefficient resolution.
-/

@[expose] public section
set_option autoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.PowerTransition
variable {C : Type u} [Category.{v} C]
section
variable [Preadditive C]

/-- Multiply every successive transition by l.
Source: simultaneous coefficient resolution in the diagonal-tower proof.
(blueprint: def-sfb-power-transition-functor). -/
def obj (l : ℕ) (X : ℕᵒᵖ ⥤ C) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ X.obj (op n))
    (fun n ↦ l • X.map (homOfLE (Nat.le_succ n)).op)

/-- Twisting keeps the components of every morphism.
Source: the same simultaneous coefficient resolution.
(blueprint: def-sfb-power-transition-functor). -/
def functor (l : ℕ) : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ C) where
  obj := obj l
  map f := NatTrans.ofOpSequence (fun n ↦ f.app (op n)) (fun n ↦ by
    dsimp only [obj]
    rw [Functor.ofOpSequence_map_homOfLE_succ,
      Functor.ofOpSequence_map_homOfLE_succ, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, f.naturality])
  map_id X := by ext n; rfl
  map_comp f g := by ext n; rfl

instance additive (l : ℕ) : (functor (C := C) l).Additive where
  map_add := by intros; ext n; rfl

/-- Multiplication by l^(n+1) is a natural map from the twisted tower to the original.
Source: simultaneous coefficient resolution in the diagonal-tower proof.
(blueprint: def-sfb-power-transition-functor). -/
def multiplication (l : ℕ) : functor (C := C) l ⟶ 𝟭 _ where
  app X := NatTrans.ofOpSequence (fun n ↦ l ^ (n + 1) • 𝟙 (X.obj (op n)))
    (fun n ↦ by
      dsimp only [functor, obj]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      change (l • X.map (homOfLE (Nat.le_succ n)).op) ≫
        (l ^ (n + 1) • 𝟙 _) = (l ^ (n + 1 + 1) • 𝟙 _) ≫
          X.map (homOfLE (Nat.le_succ n)).op
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.comp_id, Category.id_comp, smul_smul]
      simp only [pow_succ])
  naturality X Y f := by
    ext n
    simp only [NatTrans.comp_app]
    change f.app n ≫ (l ^ (n.unop + 1) • 𝟙 _) =
      (l ^ (n.unop + 1) • 𝟙 _) ≫ f.app n
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.comp_id, Category.id_comp]

end

/-- Twisting does not change the evaluated cochain map, hence preserves quasi-isomorphisms.
Source: exactness of evaluation of towers; Mathlib's quasiIso_iff_evaluation.
(blueprint: def-sfb-power-transition-functor). -/
theorem quasiIso_map [Abelian C] (l : ℕ) {P K : CochainComplex (ℕᵒᵖ ⥤ C) ℤ}
    (q : P ⟶ K) [QuasiIso q] :
    QuasiIso (((functor l).mapHomologicalComplex (.up ℤ)).map q) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro n
  change QuasiIso ((((evaluation ℕᵒᵖ C).obj n).mapHomologicalComplex (.up ℤ)).map q)
  infer_instance

end CategoryTheory.PowerTransition

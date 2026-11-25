/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Algebra.Module.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Internal left modules over an external ring

Source: Stacks Project, Tag 0DV5, proof of (2)-(3)
(blueprint: def-pod-internal-module).
-/

@[expose] public section

section

universe r v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable (R : Type r) [Ring R] (C : Type u) [Category.{v} C] [HasFiniteProducts C]

/-- Internal module operations and all module axioms, tested on generalized elements.
Source: Stacks Tag 0DV5, proof of (2)-(3) (blueprint: def-pod-internal-module).
Testing all `T ⟶ X` expresses the commutative diagrams, not merely global elements. -/
structure InternalModule where
  X : C
  add : X ⨯ X ⟶ X
  zero : ⊤_ C ⟶ X
  neg : X ⟶ X
  smul : R → (X ⟶ X)
  add_assoc : ∀ (T : C) (a b c : T ⟶ X),
    prod.lift (prod.lift a b ≫ add) c ≫ add = prod.lift a (prod.lift b c ≫ add) ≫ add
  zero_add : ∀ (T : C) (a : T ⟶ X), prod.lift (terminal.from T ≫ zero) a ≫ add = a
  add_zero : ∀ (T : C) (a : T ⟶ X), prod.lift a (terminal.from T ≫ zero) ≫ add = a
  neg_add : ∀ (T : C) (a : T ⟶ X),
    prod.lift (a ≫ neg) a ≫ add = terminal.from T ≫ zero
  add_comm : ∀ (T : C) (a b : T ⟶ X), prod.lift a b ≫ add = prod.lift b a ≫ add
  one_smul : smul 1 = 𝟙 X
  mul_smul : ∀ a b : R, smul (a * b) = smul b ≫ smul a
  smul_add : ∀ (a : R) (T : C) (b c : T ⟶ X),
    prod.lift b c ≫ add ≫ smul a = prod.lift (b ≫ smul a) (c ≫ smul a) ≫ add
  add_smul : ∀ (a b : R) (T : C) (c : T ⟶ X),
    c ≫ smul (a + b) = prod.lift (c ≫ smul a) (c ≫ smul b) ≫ add
  zero_smul : smul 0 = terminal.from X ≫ zero
  smul_zero : ∀ a : R, zero ≫ smul a = zero

namespace InternalModule

variable {R C}

/-- A map of internal modules commutes with all four operations.
Source: Stacks Tag 0DV5, proof of (3) (blueprint: def-pod-internal-module). -/
def IsHom (A B : InternalModule R C) (f : A.X ⟶ B.X) : Prop :=
  A.add ≫ f = prod.map f f ≫ B.add ∧ A.zero ≫ f = B.zero ∧
    A.neg ≫ f = f ≫ B.neg ∧ ∀ a : R, A.smul a ≫ f = f ≫ B.smul a

/-- Identity maps preserve the operations. Source: Stacks Tag 0DV5
(blueprint: def-pod-internal-module).
Proof: compose each operation with the identity and use the product identity law. -/
theorem isHom_id (A : InternalModule R C) : IsHom A A (𝟙 A.X) := by
  simp only [IsHom, Category.comp_id, Category.id_comp, prod.map_id_id, and_self,
    implies_true]

/-- Composites preserve the operations. Source: Stacks Tag 0DV5
(blueprint: def-pod-internal-module).
Proof: substitute the two compatibility equations successively, use associativity,
and use functoriality of the binary product map. -/
theorem isHom_comp (A B D : InternalModule R C) (f : A.X ⟶ B.X) (g : B.X ⟶ D.X)
    (hf : IsHom A B f) (hg : IsHom B D g) : IsHom A D (f ≫ g) := by
  rcases hf with ⟨hf_add, hf_zero, hf_neg, hf_smul⟩
  rcases hg with ⟨hg_add, hg_zero, hg_neg, hg_smul⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hf_add, Category.assoc, hg_add, ← Category.assoc,
      prod.map_map]
  · rw [← Category.assoc, hf_zero, hg_zero]
  · rw [← Category.assoc, hf_neg, Category.assoc, hg_neg, ← Category.assoc]
  · intro a
    rw [← Category.assoc, hf_smul, Category.assoc, hg_smul, ← Category.assoc]

/-- The category of internal modules, with operation-preserving morphisms.
Source: Stacks Tag 0DV5 (blueprint: def-pod-internal-module). -/
instance category : Category (InternalModule R C) where
  Hom A B := { f : A.X ⟶ B.X // IsHom A B f }
  id A := ⟨𝟙 A.X, isHom_id A⟩
  comp f g := ⟨f.val ≫ g.val, isHom_comp _ _ _ _ _ f.property g.property⟩
  id_comp _ := Subtype.ext (Category.id_comp _)
  comp_id _ := Subtype.ext (Category.comp_id _)
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

/-- Forget the internal module operations.
Source: Stacks Tag 0DV5 (blueprint: def-pod-internal-module). -/
def forget (R : Type r) [Ring R] (C : Type u) [Category.{v} C] [HasFiniteProducts C] :
    InternalModule R C ⥤ C where
  obj A := A.X
  map f := f.val

end InternalModule
end CategoryTheory

end

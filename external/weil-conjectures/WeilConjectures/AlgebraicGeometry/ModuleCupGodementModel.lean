/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # The concrete product-of-stalks Godement model

Source: Stacks Project, Tag 0FKR; Banerjee, arXiv:1004.1491, §1.1.4.
The model predicate specifies actual objects and cofaces, rather than assuming
acyclicity or a quasi-isomorphism. No data are chosen from an existence theorem.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The product of the skyscrapers of the stalks of a module sheaf.
Source: Stacks, Tag 0FKR (blueprint: def-sc-module-cup-godement-model). -/
def moduleCup_godementObject (X : Scheme.{u}) (F : X.Modules) : X.Modules :=
  ∏ᶜ fun x : X ↦ skyscraper x (F.presheaf.stalk x)

/-- The germ map into the product of stalk skyscrapers.
Source: Stacks, Tag 0FKR (blueprint: def-sc-module-cup-godement-model). -/
def moduleCup_godementUnit (X : Scheme.{u}) (F : X.Modules) :
    F ⟶ moduleCup_godementObject X F :=
  Pi.lift fun x : X ↦ toSkyscraper (LinearMap.id :
    F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x)

/-- The map between products of stalk skyscrapers induced by a module morphism.
Source: Stacks, Tag 0FKR (blueprint: def-sc-module-cup-godement-model). -/
def moduleCup_godementMap (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) :
    moduleCup_godementObject X F ⟶ moduleCup_godementObject X G :=
  Pi.lift fun x : X ↦
    Pi.π (fun y : X ↦ skyscraper y (F.presheaf.stalk y)) x ≫
      toSkyscraper (f.stalkLinearMap x ∘ₗ skyscraperStalkEval x (F.presheaf.stalk x))

/-- Iterates of the concrete product-of-stalks construction, beginning with `F`.
Source: Stacks, Tag 0FKR (blueprint: def-sc-module-cup-godement-model). -/
def moduleCup_godementIterate (X : Scheme.{u}) (F : X.Modules) : ℕ → X.Modules
  | 0 => F
  | n + 1 => moduleCup_godementObject X (moduleCup_godementIterate X F n)

/-- Insert the germ map at the specified position in an iterate.
Source: Banerjee, §1.1.4 (blueprint: def-sc-module-cup-godement-model). -/
def moduleCup_godementInsert (X : Scheme.{u}) (F : X.Modules) :
    (n : ℕ) → Fin (n + 1) →
      (moduleCup_godementIterate X F n ⟶ moduleCup_godementIterate X F (n + 1))
  | 0, _ => moduleCup_godementUnit X F
  | n + 1, i => if h : i.val = 0 then
      moduleCup_godementUnit X (moduleCup_godementIterate X F (n + 1))
    else moduleCup_godementMap X
      (moduleCup_godementInsert X F n ⟨i.val - 1, by omega⟩)

/-- A cosimplicial object and augmentation have the actual Godement terms,
unit-insertion cofaces, and degree-zero germ map. This predicate contains no
flasqueness, exactness, homology, or quasi-isomorphism assertion.
Source: Stacks, Tag 0FKR; Banerjee, §1.1.4
(blueprint: def-sc-module-cup-godement-model). -/
def ModuleCupGodementModel (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      (((alternatingCofaceMapComplex X.Modules).obj A).extend
        ComplexShape.embeddingUpNat)) : Prop :=
  ∃ h : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1),
    (∀ (n : ℕ) (i : Fin (n + 2)),
      eqToHom (h n) ≫ moduleCup_godementInsert X F (n + 1) i =
        A.map (SimplexCategory.δ i) ≫ eqToHom (h (n + 1))) ∧
    a.f 0 ≫ (((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫ eqToHom (h 0) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ≫ moduleCup_godementUnit X F

end
end AlgebraicGeometry.Scheme.Modules

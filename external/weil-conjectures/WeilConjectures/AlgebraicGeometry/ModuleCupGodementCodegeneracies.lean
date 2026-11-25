/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel

/-! # Concrete Godement multiplication and codegeneracies

These constructions specify the degeneracies in addition to the terms and
cofaces fixed by `ModuleCupGodementModel`. No existential witness is chosen.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Evaluate the outer stalk coordinate to multiply the Godement monad.
Source: Stacks, Tag 0FKR; Banerjee, §1.1.4.
(blueprint: def-sc-module-cup-godement-codegeneracies) -/
def moduleCup_godementMultiply (X : Scheme.{u}) (F : X.Modules) :
    moduleCup_godementObject X (moduleCup_godementObject X F) ⟶
      moduleCup_godementObject X F :=
  Pi.lift fun x : X ↦
    Pi.π (fun y : X ↦ skyscraper y ((moduleCup_godementObject X F).presheaf.stalk y)) x ≫
      toSkyscraper
        (skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ
          (Pi.π (fun y : X ↦ skyscraper y (F.presheaf.stalk y)) x).stalkLinearMap x ∘ₗ
          skyscraperStalkEval x ((moduleCup_godementObject X F).presheaf.stalk x))

/-- Insert monad multiplication at a specified position in an iterate.
Source: Banerjee, §1.1.4.
(blueprint: def-sc-module-cup-godement-codegeneracies) -/
def moduleCup_godementCollapse (X : Scheme.{u}) (F : X.Modules) :
    (n : ℕ) → Fin (n + 1) →
      (moduleCup_godementIterate X F (n + 2) ⟶ moduleCup_godementIterate X F (n + 1))
  | 0, _ => moduleCup_godementMultiply X F
  | n + 1, i => if h : i.val = 0 then
      moduleCup_godementMultiply X (moduleCup_godementIterate X F (n + 1))
    else moduleCup_godementMap X
      (moduleCup_godementCollapse X F n ⟨i.val - 1, by omega⟩)

/-- The codegeneracies of a concrete Godement model are multiplication insertions.
Source: Banerjee, §1.1.4.
(blueprint: def-sc-module-cup-godement-codegeneracies) -/
def ModuleCupGodementCodegeneracies (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules) : Prop :=
  ∃ h : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1),
    ∀ (n : ℕ) (i : Fin (n + 1)),
      eqToHom (h (n + 1)) ≫ moduleCup_godementCollapse X F n i =
        A.map (SimplexCategory.σ i) ≫ eqToHom (h n)

end
end AlgebraicGeometry.Scheme.Modules

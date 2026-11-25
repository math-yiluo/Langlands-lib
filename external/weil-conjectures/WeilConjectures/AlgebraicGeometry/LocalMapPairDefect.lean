/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.LocalMapPairCompatibility
@[expose] public section
open CategoryTheory
namespace CategoryTheory.Pseudofunctor.DescentData
variable {C : Type*} [Category* C]
  {P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
  {ι : Type*} {S : C} {X : ι → C} {f : ∀ a, X a ⟶ S}
  {D₁ D₂ : P.DescentData f}

/-- The difference of the two sides of the pairwise descent square vanishes on every test.
Source: Stacks Project, Tag 01ZR (3), agreement on overlaps.
(blueprint: lem-pc-fp-local-map-pair-defect-zero).
-/
def PairDefectZero (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι) : Prop :=
  ∀ ⦃W : C⦄ (t : W ⟶ S) (g₁ : W ⟶ X a) (g₂ : W ⟶ X b)
    (h₁ : g₁ ≫ f a = t) (h₂ : g₂ ≫ f b = t),
    ∃ z, (P.map g₁.op.toLoc).toFunctor.map (r a) ≫ D₂.hom t g₁ g₂ h₁ h₂ = z ∧
      D₁.hom t g₁ g₂ h₁ h₂ ≫ (P.map g₂.op.toLoc).toFunctor.map (r b) = z

/-- A vanishing pair defect is exactly the pairwise compatibility equation.
Source: Stacks Project, Tag 01ZR (3), agreement on overlaps.
(blueprint: lem-pc-fp-local-map-pair-defect-zero).

(blueprint: def-pc-local-map-pair-defect-zero)
-/
theorem pairCompatibility_of_pairDefectZero
    (r : ∀ a, D₁.obj a ⟶ D₂.obj a) (a b : ι)
    (h : PairDefectZero r a b) : PairCompatibility r a b := by
  refine ⟨?_⟩
  intro W t g₁ g₂ h₁ h₂
  obtain ⟨z, hz₁, hz₂⟩ := h t g₁ g₂ h₁ h₂
  exact hz₁.trans hz₂.symm

end CategoryTheory.Pseudofunctor.DescentData

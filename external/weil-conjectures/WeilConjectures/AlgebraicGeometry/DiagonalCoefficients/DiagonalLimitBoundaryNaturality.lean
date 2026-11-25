/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Category

/-! # Transporting a whole-system boundary through normalized endpoints

Source: blueprint diagonal coefficient changes, paragraph (3).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Naturality of a comparison of entire systems transports a boundary equation
as soon as the two endpoint squares commute.

Source: blueprint coefficient changes (3), naturality before finite evaluation.
(blueprint: lem-diagonal-limit-boundary-naturality).

Proof: postcompose with the monic target comparison. Replace the target endpoint
square, then use the defining boundary equation. Naturality moves the boundary
through the comparison, and the original boundary square identifies the result
with the new boundary. The source endpoint square and the new defining boundary
equation give the other side. Cancel the target comparison. -/
theorem diagonalLimitBoundary_naturality
    {A B A' B' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    (n : (F ⋙ V) ⟶ (U ⋙ G))
    {X Y : A} {X' Y' : A'}
    (κ : X ⟶ Y) (κ' : X' ⟶ Y')
    (a : U.obj X ⟶ X') (b : U.obj Y ⟶ Y')
    (hκ : U.map κ ≫ b = a ≫ κ')
    {P Q : B} {P' Q' : B'}
    (s : P ⟶ F.obj X) (t : Q ⟶ F.obj Y)
    (s' : P' ⟶ G.obj X') (t' : Q' ⟶ G.obj Y') [Mono t']
    (δ : P ⟶ Q) (δ' : P' ⟶ Q')
    (hδ : δ ≫ t = s ≫ F.map κ)
    (hδ' : δ' ≫ t' = s' ≫ G.map κ')
    (α : V.obj P ⟶ P') (β : V.obj Q ⟶ Q')
    (hs : V.map s ≫ n.app X ≫ G.map a = α ≫ s')
    (ht : V.map t ≫ n.app Y ≫ G.map b = β ≫ t') :
    V.map δ ≫ β = α ≫ δ' := by
  apply (cancel_mono t').1
  calc
    (V.map δ ≫ β) ≫ t' = V.map δ ≫ V.map t ≫ n.app Y ≫ G.map b := by
      rw [Category.assoc, ← ht]
    _ = V.map (δ ≫ t) ≫ n.app Y ≫ G.map b := by
      rw [V.map_comp, Category.assoc]
    _ = V.map s ≫ V.map (F.map κ) ≫ n.app Y ≫ G.map b := by
      rw [hδ, V.map_comp, Category.assoc]
    _ = V.map s ≫ n.app X ≫ G.map (U.map κ) ≫ G.map b := by
      have hn := n.naturality κ
      change V.map (F.map κ) ≫ n.app Y = n.app X ≫ G.map (U.map κ) at hn
      simpa only [Category.assoc] using
        congrArg (fun z ↦ V.map s ≫ z ≫ G.map b) hn
    _ = V.map s ≫ n.app X ≫ G.map a ≫ G.map κ' := by
      rw [← G.map_comp, hκ, G.map_comp]
    _ = (α ≫ s') ≫ G.map κ' := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ G.map κ') hs
    _ = (α ≫ δ') ≫ t' := by
      simpa only [Category.assoc] using congrArg (fun z ↦ α ≫ z) hδ'.symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

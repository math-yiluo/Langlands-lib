/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.Category

/-! # The diagram calculation for proper Kunneth normalization

Source: the proper forget-supports calculation in the first coordinate triangle.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A route calculation using the compositor, inner map, projection and tensor squares.
Source: blueprint latest, thm-amb-p1-adjunction.proof.md, first triangle
(auxiliary; not a blueprint node).

Proof: replace the final compositor followed by comparison by its supported
factorization. Combine the two maps inside F and use the inner-map square.
Naturality of eta moves the comparison left through their composite. Replace
the projection followed by comparison by the ordinary projection. Expand the
ordinary image of the composite and use projection naturality. The tensor
square moves the two coefficient comparisons past the outside swap. The ordinary
factorization then identifies the remaining path with kappa. This is an equation
in arbitrary categories, with no invertibility or nonzero-object hypothesis. -/
theorem properKunnethNormalizationAlgebra
    {D E : Type v} [Category.{u} D] [Category.{u} E]
    (F G : D ⥤ E) (eta : F ⟶ G)
    {U X X' X'' Z H H' : E} {V V' W Q : D}
    (s : U ⟶ X) (r : X ⟶ F.obj V) (i : V ⟶ W)
    (k : F.obj W ⟶ H) (ch : H ⟶ H')
    (c : W ⟶ Q) (cmp : G.obj Q ⟶ H')
    (v : V ⟶ V') (t : V' ⟶ Q)
    (b : X ⟶ X') (r' : X' ⟶ G.obj V)
    (d : X' ⟶ X'') (r'' : X'' ⟶ G.obj V')
    (input : U ⟶ Z) (s' : Z ⟶ X'') (kappa : Z ⟶ H')
    (hc : k ≫ ch = F.map c ≫ eta.app Q ≫ cmp)
    (hi : i ≫ c = v ≫ t)
    (hp : r ≫ eta.app V = b ≫ r')
    (hn : r' ≫ G.map v = d ≫ r'')
    (hs : s ≫ b ≫ d = input ≫ s')
    (hk : s' ≫ r'' ≫ G.map t ≫ cmp = kappa) :
    (s ≫ r ≫ F.map i ≫ k) ≫ ch = input ≫ kappa := by
  simp only [Category.assoc]
  rw [hc, ← F.map_comp_assoc, hi, eta.naturality_assoc, reassoc_of% hp]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hs, hk]

end AlgebraicGeometry.Etale

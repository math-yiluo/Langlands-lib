/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Monoidal.Functor

/-! # Pullback of pairings from a canonical tensorator square -/

@[expose] public section

set_option autoImplicit false

universe uC uE uD uF vC vE vD vF

open CategoryTheory MonoidalCategory

namespace CategoryTheory

/-- A canonical tensorator pullback square and naturality imply the square for pairings.
Source: Stacks, Cohomology on Sites, Tag 06YU, functoriality of derived tensor comparisons.
(auxiliary; not a blueprint node).
Proof: use naturality of the single/pullback comparison on the pairing map. Apply the
ordinary pullback square under the single functor. Its initial tensor comparison is
the assumed canonical square. Naturality of the target tensorator moves the two
remaining ordinary arrows to the tensor factors; tensor bifunctoriality combines them
with the two single/pullback components. No invertibility is required in this argument. -/
theorem flatPairing_pullback_assembly
    {C : Type uC} {E : Type uE} {D : Type uD} {F : Type uF}
    [Category.{vC} C] [Category.{vE} E] [Category.{vD} D] [Category.{vF} F]
    [MonoidalCategory C] [MonoidalCategory E]
    [MonoidalCategory D] [MonoidalCategory F]
    (S : C ⥤ D) (S' : E ⥤ F) (U : C ⥤ E) (V : D ⥤ F)
    (γ : S ⋙ V ⟶ U ⋙ S') (P : C → Prop) (P' : E → Prop)
    (μ : ∀ L M : C, P L → (S.obj L ⊗ S.obj M ⟶ S.obj (L ⊗ M)))
    (μ' : ∀ L M : E, P' L → (S'.obj L ⊗ S'.obj M ⟶ S'.obj (L ⊗ M)))
    (δ : ∀ L M : C, U.obj (L ⊗ M) ⟶ U.obj L ⊗ U.obj M)
    (κ : ∀ L M : C,
      V.obj (S.obj L ⊗ S.obj M) ⟶ V.obj (S.obj L) ⊗ V.obj (S.obj M))
    (hU : ∀ {L : C}, P L → P' (U.obj L))
    (h_natural : ∀ {L L' M M' : E} (b : L ⟶ L') (c : M ⟶ M')
      (hL : P' L) (hL' : P' L'),
      (S'.map b ⊗ₘ S'.map c) ≫ μ' L' M' hL' = μ' L M hL ≫ S'.map (b ⊗ₘ c))
    (h_pull : ∀ (L M : C) (hL : P L),
      V.map (μ L M hL) ≫ γ.app (L ⊗ M) ≫ S'.map (δ L M) =
        κ L M ≫ (γ.app L ⊗ₘ γ.app M) ≫ μ' (U.obj L) (U.obj M) (hU hL))
    {L M N : C} {L' M' N' : E} (hL : P L) (hL' : P' L')
    (f : L ⊗ M ⟶ N) (g : L' ⊗ M' ⟶ N')
    (b : U.obj L ⟶ L') (c : U.obj M ⟶ M') (d : U.obj N ⟶ N')
    (w : U.map f ≫ d = δ L M ≫ (b ⊗ₘ c) ≫ g) :
    V.map (μ L M hL ≫ S.map f) ≫ γ.app N ≫ S'.map d =
      κ L M ≫ (γ.app L ≫ S'.map b) ▷ V.obj (S.obj M) ≫
        S'.obj L' ◁ (γ.app M ≫ S'.map c) ≫ (μ' L' M' hL' ≫ S'.map g) := by
  have nf : V.map (S.map f) ≫ γ.app N =
      γ.app (L ⊗ M) ≫ S'.map (U.map f) := γ.naturality f
  have nbc := h_natural b c (hU hL) hL'
  rw [V.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% nf, ← S'.map_comp, w]
  simp only [S'.map_comp]
  rw [reassoc_of% (h_pull L M hL), ← reassoc_of% nbc,
    tensorHom_comp_tensorHom_assoc]
  simp only [tensorHom_def, Category.assoc]

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Category.Preorder

/-! # Transport of an adjunction mate along an isomorphism of diagrams

Source: Stacks Project, Tag 02N7, mate construction; Tag 0B65, adjunction conjugation.
(blueprint: lem-weil-pbc-formal-system-exchange-mate-compatibility).
-/

@[expose] public section
set_option autoImplicit false
open CategoryTheory Opposite

namespace AlgebraicGeometry

private theorem exchange_unit
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    (L : D ⥤ C) (P : C ⥤ D) (T : D ⥤ E) (U : C ⥤ A)
    (R : E ⥤ A) (Q : A ⥤ E) (adj : L ⊣ P) (adjR : R ⊣ Q)
    (c : T ⋙ R ≅ L ⋙ U) (B : P ⋙ T ⟶ U ⋙ Q)
    (hmate : ∀ N : D, T.map (adj.unit.app N) ≫ B.app (L.obj N) =
      adjR.unit.app (T.obj N) ≫ Q.map (c.hom.app N))
    {N : D} {N₀ : E} {M : C} {M₀ : A} (a : N₀ ⟶ T.obj N)
    (β : L.obj N ⟶ M) (e : U.obj M ⟶ M₀) :
    a ≫ T.map (adj.unit.app N ≫ P.map β) ≫ (B.app M ≫ Q.map e) =
      adjR.unit.app N₀ ≫ Q.map (R.map a ≫ c.hom.app N ≫ U.map β ≫ e) := by
  have hn := B.naturality β
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (T.map (P.map β)) (B.app M), hn]
  simp only [Category.assoc]
  rw [← Category.assoc (T.map (adj.unit.app N)) (B.app (L.obj N)), hmate]
  simp only [Category.assoc]
  have hunit := adjR.unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hunit
  rw [← Category.assoc a (adjR.unit.app (T.obj N)), hunit]
  simp only [Category.assoc]

/-- A mate identity on objects transports to isomorphic diagrams.
Source: Stacks Project, Tag 02N7 (adjunction mate construction) and Tag 0B65.
(blueprint: lem-weil-pbc-formal-system-exchange-mate-compatibility).

Proof: Evaluate at a level n. Expand pullback of the composite unit and beta.
Naturality of B at beta moves beta after B at L(G_n). Substitute the supplied
objectwise mate identity. Naturality of the R-adjunction unit at the component
of eqToHom hG moves that component inside Q of R. Functoriality of Q identifies
the resulting four arrows with the component of the displayed transported beta.
Whiskering and vertical composition give the displayed component of t.
This uses no coherence, ideals, invertibility of B, flatness or scheme properties. -/
theorem formal_system_exchange_mate_compatibility
    {C D E A : Type*} [Category C] [Category D] [Category E] [Category A]
    (L : D ⥤ C) (P : C ⥤ D) (T : D ⥤ E) (U : C ⥤ A)
    (R : E ⥤ A) (Q : A ⥤ E) (adj : L ⊣ P) (adjR : R ⊣ Q)
    (c : T ⋙ R ≅ L ⋙ U) (B : P ⋙ T ⟶ U ⋙ Q)
    (hmate : ∀ N : D, T.map (adj.unit.app N) ≫ B.app (L.obj N) =
      adjR.unit.app (T.obj N) ≫ Q.map (c.hom.app N))
    (G : ℕᵒᵖ ⥤ D) (G₀ : ℕᵒᵖ ⥤ E) (hG : G₀ = G ⋙ T)
    (H : ℕᵒᵖ ⥤ C) (H₀ : ℕᵒᵖ ⥤ A) (β : G ⋙ L ≅ H) (e : H ⋙ U ≅ H₀) :
    ∃ (β₀ : G₀ ⋙ R ≅ H₀) (t : (H ⋙ P) ⋙ T ⟶ H₀ ⋙ Q),
      t = Functor.whiskerLeft H B ≫ Functor.whiskerRight e.hom Q ∧
      (∀ n : ℕ, (eqToHom hG).app (op n) ≫
          T.map (adj.unit.app (G.obj (op n)) ≫ P.map (β.hom.app (op n))) ≫
            t.app (op n) =
        adjR.unit.app (G₀.obj (op n)) ≫ Q.map (β₀.hom.app (op n))) := by
  let β₀ : G₀ ⋙ R ≅ H₀ := Functor.isoWhiskerRight (eqToIso hG) R ≪≫
    Functor.isoWhiskerLeft G c ≪≫ Functor.isoWhiskerRight β U ≪≫ e
  let t : (H ⋙ P) ⋙ T ⟶ H₀ ⋙ Q :=
    Functor.whiskerLeft H B ≫ Functor.whiskerRight e.hom Q
  refine ⟨β₀, t, rfl, ?_⟩
  intro n
  have hβ₀ : β₀.hom.app (op n) =
      R.map ((eqToHom hG).app (op n)) ≫ c.hom.app (G.obj (op n)) ≫
        U.map (β.hom.app (op n)) ≫ e.hom.app (op n) := rfl
  change (eqToHom hG).app (op n) ≫
    T.map (adj.unit.app (G.obj (op n)) ≫ P.map (β.hom.app (op n))) ≫
      (B.app (H.obj (op n)) ≫ Q.map (e.hom.app (op n))) = _
  rw [hβ₀]
  exact exchange_unit L P T U R Q adj adjR c B hmate
    ((eqToHom hG).app (op n)) (β.hom.app (op n)) (e.hom.app (op n))

end AlgebraicGeometry

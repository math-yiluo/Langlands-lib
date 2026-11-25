/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Transport of adjunction-induced transitions along base change

Given adjunctions `E₀ ⊣ R₀`, `E₁ ⊣ R₁` with `Q ⋙ R₁ ≅ R₀`, the transition
`R₁ E₁ ⟶ R₀ E₀` is induced by the adjoint of the unit. Base change isomorphisms between
two such configurations, compatible with the units and with the comparison isomorphisms,
intertwine the transitions.

(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {A A' B₀ B₁ B₀' B₁' : Type*} [Category A] [Category A'] [Category B₀] [Category B₁]
  [Category B₀'] [Category B₁']
  {E₀ : A ⥤ B₀} {R₀ : B₀ ⥤ A} (adj₀ : E₀ ⊣ R₀)
  {E₁ : A ⥤ B₁} {R₁ : B₁ ⥤ A} (adj₁ : E₁ ⊣ R₁)
  {E₀' : A' ⥤ B₀'} {R₀' : B₀' ⥤ A'} (adj₀' : E₀' ⊣ R₀')
  {E₁' : A' ⥤ B₁'} {R₁' : B₁' ⥤ A'} (adj₁' : E₁' ⊣ R₁')
  {Q : B₀ ⥤ B₁} {Q' : B₀' ⥤ B₁'} (c : Q ⋙ R₁ ≅ R₀) (c' : Q' ⋙ R₁' ≅ R₀')

/-- The adjoint of the unit followed by the comparison. (auxiliary; not a blueprint node). -/
def towerReduction (K : A) : E₁.obj K ⟶ Q.obj (E₀.obj K) :=
  (adj₁.homEquiv _ _).symm (adj₀.unit.app K ≫ c.inv.app (E₀.obj K))

/-- The induced transition. (auxiliary; not a blueprint node). -/
def towerTransition (K : A) : R₁.obj (E₁.obj K) ⟶ R₀.obj (E₀.obj K) :=
  R₁.map (towerReduction adj₀ adj₁ c K) ≫ c.hom.app (E₀.obj K)

variable (Ψ : A' ⥤ A) (M₀ : B₀' ⥤ B₀) (M₁ : B₁' ⥤ B₁)
  (σ₀ : R₀' ⋙ Ψ ≅ M₀ ⋙ R₀) (σ₁ : R₁' ⋙ Ψ ≅ M₁ ⋙ R₁)
  (s : Q' ⋙ M₁ ≅ M₀ ⋙ Q)
  (β₀ : Ψ ⋙ E₀ ≅ E₀' ⋙ M₀) (β₁ : Ψ ⋙ E₁ ≅ E₁' ⋙ M₁)

/-- The base change comparison of the composite functors.
(auxiliary; not a blueprint node). -/
def towerBaseChange (σ : R₀' ⋙ Ψ ≅ M₀ ⋙ R₀) (β : Ψ ⋙ E₀ ≅ E₀' ⋙ M₀) (K : A') :
    Ψ.obj (R₀'.obj (E₀'.obj K)) ≅ R₀.obj (E₀.obj (Ψ.obj K)) :=
  σ.app (E₀'.obj K) ≪≫ R₀.mapIso (β.app K).symm

include adj₀ adj₁ adj₀' adj₁' in
/-- Base change intertwines the transitions. (auxiliary; not a blueprint node).
Proof: transpose the reduction maps along `E₁ ⊣ R₁`. The unit compatibilities of the base
change isomorphisms and the coherence of the comparison isomorphisms identify the two
adjoints; whiskering by `R₁` and the comparison gives the transitions. -/
theorem towerTransition_baseChange
    (hβ₀ : ∀ K : A', Ψ.map (adj₀'.unit.app K) ≫ σ₀.hom.app (E₀'.obj K) =
      adj₀.unit.app (Ψ.obj K) ≫ R₀.map (β₀.hom.app K))
    (hβ₁ : ∀ K : A', Ψ.map (adj₁'.unit.app K) ≫ σ₁.hom.app (E₁'.obj K) =
      adj₁.unit.app (Ψ.obj K) ≫ R₁.map (β₁.hom.app K))
    (hc : ∀ Y : B₀', Ψ.map (c'.hom.app Y) ≫ σ₀.hom.app Y =
      σ₁.hom.app (Q'.obj Y) ≫ R₁.map (s.hom.app Y) ≫ c.hom.app (M₀.obj Y))
    (K : A') :
    Ψ.map (towerTransition adj₀' adj₁' c' K) ≫ (towerBaseChange Ψ M₀ σ₀ β₀ K).hom =
      (towerBaseChange Ψ M₁ σ₁ β₁ K).hom ≫ towerTransition adj₀ adj₁ c (Ψ.obj K) := by
  -- the transposed key equation
  have hc' : Ψ.map (c'.inv.app (E₀'.obj K)) ≫ σ₁.hom.app (Q'.obj (E₀'.obj K)) =
      σ₀.hom.app (E₀'.obj K) ≫ c.inv.app (M₀.obj (E₀'.obj K)) ≫
        R₁.map (s.inv.app (E₀'.obj K)) := by
    have h := hc (E₀'.obj K)
    rw [← cancel_epi (Ψ.map (c'.hom.app (E₀'.obj K))), ← Category.assoc, ← Ψ.map_comp,
      Iso.hom_inv_id_app, Ψ.map_id, Category.id_comp, reassoc_of% h]
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← R₁.map_comp, Iso.hom_inv_id_app]
    simp
  have key : β₁.hom.app K ≫ M₁.map (towerReduction adj₀' adj₁' c' K) =
      towerReduction adj₀ adj₁ c (Ψ.obj K) ≫ Q.map (β₀.hom.app K) ≫
        s.inv.app (E₀'.obj K) := by
    apply (adj₁.homEquiv _ _).injective
    rw [adj₁.homEquiv_unit, adj₁.homEquiv_unit, R₁.map_comp, R₁.map_comp, R₁.map_comp,
      ← Category.assoc, ← hβ₁ K]
    have h₁ : adj₁.unit.app (Ψ.obj K) ≫ R₁.map (towerReduction adj₀ adj₁ c (Ψ.obj K)) =
        adj₀.unit.app (Ψ.obj K) ≫ c.inv.app (E₀.obj (Ψ.obj K)) := by
      exact (adj₁.homEquiv_unit _ _ _).symm.trans ((adj₁.homEquiv _ _).apply_symm_apply _)
    have h₁' : adj₁'.unit.app K ≫ R₁'.map (towerReduction adj₀' adj₁' c' K) =
        adj₀'.unit.app K ≫ c'.inv.app (E₀'.obj K) := by
      exact (adj₁'.homEquiv_unit _ _ _).symm.trans ((adj₁'.homEquiv _ _).apply_symm_apply _)
    rw [reassoc_of% h₁]
    have hn := σ₁.hom.naturality (towerReduction adj₀' adj₁' c' K)
    simp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← Ψ.map_comp, h₁', Ψ.map_comp,
      Category.assoc, hc', ← Category.assoc, ← Category.assoc, hβ₀ K]
    have hn' := c.inv.naturality (β₀.hom.app K)
    simp only [Functor.comp_obj, Functor.comp_map] at hn'
    simp only [Category.assoc]
    rw [reassoc_of% hn']
  have key' : M₁.map (towerReduction adj₀' adj₁' c' K) ≫ s.hom.app (E₀'.obj K) ≫
      Q.map (β₀.inv.app K) = β₁.inv.app K ≫ towerReduction adj₀ adj₁ c (Ψ.obj K) := by
    rw [← cancel_epi (β₁.hom.app K), reassoc_of% key]
    simp [← Functor.map_comp]
  change Ψ.map (R₁'.map (towerReduction adj₀' adj₁' c' K) ≫ c'.hom.app (E₀'.obj K)) ≫
      σ₀.hom.app (E₀'.obj K) ≫ R₀.map (β₀.inv.app K) =
    (σ₁.hom.app (E₁'.obj K) ≫ R₁.map (β₁.inv.app K)) ≫
      R₁.map (towerReduction adj₀ adj₁ c (Ψ.obj K)) ≫ c.hom.app (E₀.obj (Ψ.obj K))
  rw [Ψ.map_comp, Category.assoc, reassoc_of% (hc (E₀'.obj K))]
  have hn := σ₁.hom.naturality (towerReduction adj₀' adj₁' c' K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  have hn' := c.hom.naturality (β₀.inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hn'
  rw [reassoc_of% hn, ← hn']
  simp only [Category.assoc, ← Functor.map_comp_assoc, key']

end CategoryTheory.Adjunction

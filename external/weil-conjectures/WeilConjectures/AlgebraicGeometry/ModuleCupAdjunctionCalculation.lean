/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.CategoryTheory.Monoidal.Functor
@[expose] public section
open CategoryTheory MonoidalCategory
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme.Modules
/-- Adjunction transposition combines the tensor, evaluation and comparison squares.
Source: Stacks, Tag 0FP3, the adjunction calculation in the proof of Lemma 20.31.3.
(blueprint: lem-sc-module-cup-polygon-calculation) -/
theorem moduleCup_polygon_calculation
    {C C₀ E E₀ : Type*} [Category* C] [Category* C₀] [Category* E] [Category* E₀]
    [MonoidalCategory C] [MonoidalCategory C₀]
    [MonoidalCategory E] [MonoidalCategory E₀]
    (Q : C ⥤ E) [Q.LaxMonoidal] (Q₀ : C₀ ⥤ E₀) [Q₀.LaxMonoidal]
    (T : C ⥤ C₀) (F : C₀ ⥤ C) (D : E₀ ⥤ E) (R : E ⥤ E₀)
    (adj : F ⊣ T) (dAdj : D ⊣ R)
    (a : Q₀ ⋙ D ⟶ F ⋙ Q) (b : T ⋙ Q₀ ⟶ Q ⋙ R)
    (δ : ∀ A B, D.obj (A ⊗ B) ≅ D.obj A ⊗ D.obj B)
    (hNat : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      D.map (f ⊗ₘ g) ≫ (δ A' B').hom =
        (δ A B).hom ≫ (D.map f ⊗ₘ D.map g))
    (t : ∀ A B, F.obj (A ⊗ B) ⟶ F.obj A ⊗ F.obj B)
    (ht : ∀ A B, D.map (Functor.LaxMonoidal.μ Q₀ A B) ≫ a.app (A ⊗ B) ≫
      Q.map (t A B) = (δ (Q₀.obj A) (Q₀.obj B)).hom ≫
        (a.app A ⊗ₘ a.app B) ≫ Functor.LaxMonoidal.μ Q (F.obj A) (F.obj B))
    (hc : ∀ K, D.map (b.app K) ≫ dAdj.counit.app (Q.obj K) =
      a.app (T.obj K) ≫ Q.map (adj.counit.app K))
    (K L I : C) (m : T.obj K ⊗ T.obj L ⟶ T.obj (K ⊗ L))
    (ho : F.map m ≫ adj.counit.app (K ⊗ L) =
      t (T.obj K) (T.obj L) ≫ (adj.counit.app K ⊗ₘ adj.counit.app L))
    (φ : K ⊗ L ⟶ I) :
    (b.app K ⊗ₘ b.app L) ≫
      dAdj.homEquiv _ _ ((δ _ _).hom ≫
        (dAdj.counit.app (Q.obj K) ⊗ₘ dAdj.counit.app (Q.obj L))) ≫
      R.map (Functor.LaxMonoidal.μ Q K L ≫ Q.map φ) =
    Functor.LaxMonoidal.μ Q₀ (T.obj K) (T.obj L) ≫ Q₀.map (m ≫ T.map φ) ≫
      b.app I := by
  have base :
      (b.app K ⊗ₘ b.app L) ≫
        dAdj.homEquiv _ _ ((δ _ _).hom ≫
          (dAdj.counit.app (Q.obj K) ⊗ₘ dAdj.counit.app (Q.obj L))) ≫
        R.map (Functor.LaxMonoidal.μ Q K L) =
      Functor.LaxMonoidal.μ Q₀ (T.obj K) (T.obj L) ≫ Q₀.map m ≫
        b.app (K ⊗ L) := by
    apply (dAdj.homEquiv _ _).symm.injective
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
      Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      Functor.comp_obj, Functor.id_obj]
    have hn := Functor.LaxMonoidal.μ_natural Q
      (adj.counit.app K) (adj.counit.app L)
    simp only [Functor.id_obj, Functor.comp_obj] at hn
    rw [reassoc_of% (hNat _ _ _ _ (b.app K) (b.app L)),
      tensorHom_comp_tensorHom_assoc, hc K, hc L, ← tensorHom_comp_tensorHom_assoc,
      hn,
      ← reassoc_of% (ht (T.obj K) (T.obj L))]
    rw [← Q.map_comp, ← ho, Q.map_comp, hc (K ⊗ L)]
    have ha := a.naturality m
    simp only [Functor.comp_map] at ha
    rw [reassoc_of% ha]
  have bn := b.naturality φ
  simp only [Functor.comp_map] at bn
  have h := congrArg (fun f ↦ f ≫ R.map (Q.map φ)) base
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  rw [← bn] at h
  exact h
end AlgebraicGeometry.Scheme.Modules

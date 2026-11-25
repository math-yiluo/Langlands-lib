/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Projective

/-! Base-degree lifting for a free module into an exact augmentation.
Source: literature/stacks-project/algebra.tex, Tag 00LS.
(blueprint: lem-weil-pbc-free-complex-base-lift).
-/

@[expose] public section

universe u

open CategoryTheory

set_option linter.style.haveILetI false in
/-- The degree-zero lifting step in the comparison of a free complex with a
resolution.  This is the projectivity lifting argument for the augmentation.
Source: Algebra, Tag 00LS, proof of lemma-compare-resolutions (1), lines 17525--17527.
(blueprint: lem-weil-pbc-free-complex-base-lift). -/
theorem free_complex_base_lift
    (R : Type u) [CommRing R]
    (M N : ModuleCat R) (φ : M ⟶ N)
    (N' : ℕ → ModuleCat R) (η : N' 0 ⟶ N)
    (F : ℕ → ModuleCat R) (π : F 0 ⟶ M)
    (hη : Function.Surjective η)
    (hfree : Module.Free R (F 0)) :
    ∃ a₀ : F 0 ⟶ N' 0, a₀ ≫ η = π ≫ φ := by
  haveI : Module.Projective R (F 0) := Module.Projective.of_free
  obtain ⟨a, ha⟩ := Module.projective_lifting_property (P := (F 0))
    (M := (N' 0)) (N := N) η.hom (φ.hom.comp π.hom) hη
  refine ⟨ModuleCat.ofHom a, ?_⟩
  exact ModuleCat.hom_ext ha

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Degreewise middle maps for horseshoe rows

Source: the classical horseshoe naturality argument of Weibel, Theorem 2.4.6,
using Stacks Project, Tags 0136, 013R, 013P and 013T
(blueprint: lem-weil-pbc-horseshoe-degreewise-map).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

set_option backward.isDefEq.respectTransparency false in
/-- Choose the degreewise splittings of the two short exact rows using injectivity
of their first terms. If r is the source retraction and s' the target section, set
`t n = r n ≫ φA.f n ≫ α'.f n + β.f n ≫ φC.f n ≫ s' n`.
Distribute composition over addition and use αr = 1, s'β' = 1 and the two zero
composites. This yields the two squares, without claiming differential compatibility.
Source: Stacks Project, homology.tex, Tag 0136; horseshoe naturality Step 1.
(blueprint: lem-weil-pbc-horseshoe-degreewise-map) -/
theorem horseshoe_degreewise_map
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y Z X' Y' Z' : CochainComplex C ℕ}
    (α : X ⟶ Y) (β : Y ⟶ Z) (α' : X' ⟶ Y') (β' : Y' ⟶ Z')
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hexact : ∀ n : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (hexact' : ∀ n : ℕ, ((ShortComplex.mk α' β' hαβ').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (hinj : ∀ n, Injective (X.X n)) (hinj' : ∀ n, Injective (X'.X n))
    (φA : X ⟶ X') (φC : Z ⟶ Z') :
    ∃ t : ∀ n, Y.X n ⟶ Y'.X n,
      (∀ n, α.f n ≫ t n = φA.f n ≫ α'.f n) ∧
      (∀ n, t n ≫ β'.f n = β.f n ≫ φC.f n) := by
  classical
  let r : ∀ n, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).Splitting := fun n ↦ by
    have : Injective (((ShortComplex.mk α β hαβ).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).X₁) := hinj n
    exact (hexact n).splittingOfInjective
  let r' : ∀ n, ((ShortComplex.mk α' β' hαβ').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).Splitting := fun n ↦ by
    have : Injective (((ShortComplex.mk α' β' hαβ').map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).X₁) := hinj' n
    exact (hexact' n).splittingOfInjective
  let R : ∀ n, Y.X n ⟶ X.X n := fun n ↦ (r n).r
  let Q : ∀ n, Z'.X n ⟶ Y'.X n := fun n ↦ (r' n).s
  refine ⟨fun n ↦ R n ≫ φA.f n ≫ α'.f n +
    β.f n ≫ φC.f n ≫ Q n, ?_, ?_⟩
  · intro n
    have hr : α.f n ≫ R n = 𝟙 _ := (r n).f_r
    have hz := HomologicalComplex.congr_hom hαβ n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
    rw [Preadditive.comp_add, ← Category.assoc, ← Category.assoc, hr, Category.id_comp,
      ← Category.assoc, ← Category.assoc, hz, zero_comp, zero_comp, add_zero]
  · intro n
    have hs : Q n ≫ β'.f n = 𝟙 _ := (r' n).s_g
    have hz := HomologicalComplex.congr_hom hαβ' n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, hz, comp_zero,
      comp_zero, zero_add, Category.assoc, Category.assoc, hs, Category.comp_id]


end CategoryTheory.InjectiveResolution

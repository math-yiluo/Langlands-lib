/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Functoriality of the categorical trace

The categorical trace `CategoryTheory.MonoidalCategory.trace` of an endomorphism of an object `X`
of a braided monoidal category does not depend on the choice of the right dual of `X`
(`CategoryTheory.MonoidalCategory.trace_eq_of_exactPairing`, in
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided`), and it is preserved by monoidal
functors which are compatible with the braidings on the pair `(X, Xᘁ)`
(`CategoryTheory.MonoidalCategory.trace_map`).

These are used for blueprint `proposition-properties-trace`: the trace of an endomorphism of a
perfect complex in the derived category is computed in the category of complexes, where it is the
supertrace (blueprint `proposition-properties-trace--4`).
-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

open Category Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Monoidal]

/-- A monoidal functor `F` which is compatible with the braidings on the pair `(X, Xᘁ)` preserves
categorical traces: `tr(F f) = F(tr f)`, up to the identification `𝟙_ D ≅ F (𝟙_ C)`. The
right dual of `F X` is arbitrary. -/
theorem trace_map {X : C} [HasRightDual X] [HasRightDual (F.obj X)]
    (hF : μ F X Xᘁ ≫ F.map (β_ X Xᘁ).hom = (β_ (F.obj X) (F.obj Xᘁ)).hom ≫ μ F Xᘁ X)
    (f : X ⟶ X) : trace (F.map f) = ε F ≫ F.map (trace f) ≫ η F := by
  let := ExactPairing.map F X Xᘁ
  rw [trace_eq_of_exactPairing (Y := F.obj Xᘁ)]
  have hη : η_ (F.obj X) (F.obj Xᘁ) = ε F ≫ F.map (η_ X Xᘁ) ≫ δ F X Xᘁ := rfl
  have hε : ε_ (F.obj X) (F.obj Xᘁ) = μ F Xᘁ X ≫ F.map (ε_ X Xᘁ) ≫ η F := rfl
  have hβ : δ F X Xᘁ ≫ (β_ (F.obj X) (F.obj Xᘁ)).hom ≫ μ F Xᘁ X = F.map (β_ X Xᘁ).hom := by
    rw [← hF, Functor.Monoidal.δ_μ_assoc]
  rw [hη, hε, trace]
  simp only [assoc, Functor.map_comp]
  rw [δ_natural_left_assoc, reassoc_of% hβ]

end CategoryTheory.MonoidalCategory

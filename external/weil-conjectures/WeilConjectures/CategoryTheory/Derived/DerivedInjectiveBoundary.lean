/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Normalized connecting maps for a sequence exact on injectives

Source: Stacks Project, Tags 0117, 05TI, 05TH and 070I; Milne,
Lectures on Etale Cohomology, Section 9, Theorem 9.4.
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe v u w a
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A : Type a} [Category.{w} A] [Abelian A]
  [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C]

variable (S F G : C ⥤ A) [S.Additive] [F.Additive] [G.Additive]
  (ι : S ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)

omit [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C] in
omit [HasDerivedCategory C] [HasDerivedCategory A] [EnoughInjectives C] in
/-- Exactness transports through a specified commuting triple of isomorphisms.
Source: Stacks, Tag 0117. -/
theorem exact_transport {R : ShortComplex A} (hR : R.Exact)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e₁ : R.X₁ ≅ X) (e₂ : R.X₂ ≅ Y) (e₃ : R.X₃ ≅ Z)
    (h₁ : e₁.hom ≫ f = R.f ≫ e₂.hom)
    (h₂ : e₂.hom ≫ g = R.g ≫ e₃.hom) :
    ∃ w : f ≫ g = 0, (ShortComplex.mk f g w).Exact := by
  have w : f ≫ g = 0 := by
    apply (cancel_epi e₁.hom).1
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc, R.zero]
    simp
  exact ⟨w, ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂) hR⟩

end CategoryTheory.Functor

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-!
# The native cochain localization tensorator

Source: Stacks Project, sites-cohomology.tex, Tag 07A4, representative tensor calculation.
The cochain localization is the composite of the homotopy quotient and `Qh`, transported
along `quotientCompQhIso`. Its tensorator is therefore the homotopy tensorator with
identity comparison factors on both sides. Expanding that transport cancels these factors.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.Functor

/-- The native cochain tensorator is the homotopy tensorator on quotient objects.

Proof. The lax structure on `Q` is `LaxMonoidal.ofIso (quotientCompQhIso C)`. Its
component is `(1 ⊗ 1) ≫ (μ Qh ≫ Qh.map 1) ≫ 1`, since both quotient comparisons
and the tensorator of the homotopy quotient are identities. Apply functoriality and
the identity laws. No tensorator is inverted.
(blueprint: lem-sf-finite-open-mixed-tensor-representative-counit-transport) -/
theorem cochainLocalization_tensorator_eq
    {C : Type*} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (P Q : CochainComplex C ℤ) :
    LaxMonoidal.μ DerivedCategory.Q P Q =
      cast (by rfl) (LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q)) := by
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ (_ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ 𝟙 _ = _
  simp only [tensorHom_id, id_whiskerRight, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, cast_eq]

end CategoryTheory.Functor

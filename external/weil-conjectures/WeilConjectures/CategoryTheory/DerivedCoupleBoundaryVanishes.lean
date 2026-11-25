/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.ExactCouple
import WeilConjectures.CategoryTheory.DerivedCoupleMapConstruction
@[expose] public section
universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple
/-- (blueprint: lem-sp-derived-couple-boundary-vanishes)
The image of the incoming alpha maps to zero in the cycle quotient.
This is the boundary calculation in Stacks Tag 011R. -/
theorem derived_couple_boundary_vanishes {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X : BigradedExactCouple C s) :
    ∀ p q : ℤ,
      kernel.ι (factorThruImage (X.alpha (p + 1) (q - 1))) ≫
        X.gToCycles (p + 1) (q - 1) ≫
          X.derivedEProjection ((p + 1) + s) ((q - 1) - s) = 0 := by
  intro p q
  have hβ : ∀ p q, X.dInto p q ≫ X.f p q ≫ X.g (p + 2) (q - 1) = 0 :=
    X.dInto_comp_d
  have hβeq : ∀ p q, X.dInto p q =
      (X.f (p - s - 2) (q + s + 1) ≫
        X.g ((p - s - 2) + 2) ((q + s + 1) - 1)) ≫
          eqToHom (by congr 1 <;> omega) := fun _ _ ↦ rfl
  obtain ⟨g', hg'⟩ := derivedCoupleBackward_exists X.D X.E X.alpha X.f X.g
    X.dInto hβ X.f_g_zero X.exact_alpha hβeq p q
  have hz := kernel.ι (factorThruImage (X.alpha (p + 1) (q - 1))) ≫= hg'
  simp only [← Category.assoc, kernel.condition, zero_comp] at hz
  apply (cancel_mono (eqToHom (show
    X.derivedE ((p + 1) + s) ((q - 1) - s) =
      X.derivedE (p + (s + 1)) (q - (s + 1)) by congr 1 <;> omega))).mp
  simpa only [gToCycles, derivedEProjection, derivedE, d, Category.assoc, zero_comp]
    using hz.symm
end CategoryTheory.BigradedExactCouple

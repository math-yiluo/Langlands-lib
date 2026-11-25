/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import all WeilConjectures.CategoryTheory.FinitePageGradedQuotient
import all WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel

/-! # Transport of half-plane abutments along an exact functor -/

@[expose] public section

set_option autoImplicit false
universe u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
private theorem finite_g_factors (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ) :
    (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q) :=
  Subobject.factors_of_le _ ((L.Z_glb p q).1 ⟨r, rfl⟩)
    (X.g_factors_limitCycles L p q)
private noncomputable def finiteG (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (r : ℕ) (p q : ℤ) :
    X.D p q ⟶ (X.pageCouple r).E p q :=
  (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q)
    (finite_g_factors X L r p q) ≫ X.cycleBoundaryTower.projection r p q
section Naturality
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
omit [Abelian C] [Abelian B] [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
theorem transport_square {F : ℤ → ℤ → C} {G : ℤ → ℤ → B}
    (t : ∀ p q, Φ.obj (F p q) ⟶ G p q)
    {p q p' q' : ℤ} (hp : p = p') (hq : q = q') :
    Φ.map (eqToHom (congrArg₂ F hp hq)) ≫ t p' q' =
      t p q ≫ eqToHom (congrArg₂ G hp hq) := by
  subst p'; subst q'; simp
end Naturality

end CategoryTheory.BigradedExactCouple

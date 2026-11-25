/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictPerfectPackageOnSite

/-!
# Strict-perfect packages with independent site universes

Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
The original package is reexported; this interface retains the small pro-etale site.
-/

@[expose] public section

set_option autoImplicit false
attribute [instance] CategoryTheory.module_overFunctor_preservesZero

universe u v w r

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Degreewise finite-free splittings with independent site and coefficient universes.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
structure StrictPerfectCoefficientPackageOnSite {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
    (F : CochainComplex (SheafOfModules.{r} R) ℤ) where
  /-- Finite rank in each degree, including zero. -/
  N : ℤ → ℕ
  /-- Degreewise inclusion. -/
  i (n : ℤ) : F.X n ⟶ ∏ᶜ fun _ : Fin (N n) ↦ SheafOfModules.unit R
  /-- Degreewise retraction. -/
  p (n : ℤ) : (∏ᶜ fun _ : Fin (N n) ↦ SheafOfModules.unit R) ⟶ F.X n
  /-- Splitting without any chain-map requirement. -/
  splitting (n : ℤ) : i n ≫ p n = 𝟙 (F.X n)

end SheafOfModules

namespace SheafOfModules

section SmallRingedSite

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}

/-- Local perfectness: covering sieves admit bounded, finite-free retract models mapping
quasi-isomorphically to the restricted complex. Bounds and ranks vary with the cover member.
Source: Stacks, Tag 08G5, and proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsLocallyStrictPerfectComplexOnSite (R : Sheaf J CommRingCat.{u + 1})
    (K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ F : CochainComplex (SheafOfModules.{u + 1}
          (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) ℤ,
        (∃ a b : ℤ, ∀ r : ℤ, r < a ∨ b < r → IsZero (F.X r)) ∧
        Nonempty (StrictPerfectCoefficientPackageOnSite _ F) ∧
        ∃ α : F ⟶ ((SheafOfModules.overFunctor _ U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K, QuasiIso α

/-- Perfect objects are exactly the objects represented by locally perfect complexes.
Source: Stacks, Tag 08G5, and proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsPerfectOnSmallRingedSite (R : Sheaf J CommRingCat.{u + 1})
    [HasDerivedCategory.{w} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
    (E : DerivedCategory (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))) : Prop :=
  ∃ K : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ,
    IsLocallyStrictPerfectComplexOnSite R K ∧ Nonempty (E ≅ DerivedCategory.Q.obj K)

end SmallRingedSite

end SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- A site-perfect derived object is represented by a locally strictly perfect complex.
Source: Stacks, Tag 08G5; proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsProEtaleSitePerfect (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (Q : DerivedCategory (proEtaleRingModules X R)) : Prop :=
  SheafOfModules.IsPerfectOnSmallRingedSite R Q

end AlgebraicGeometry.Scheme

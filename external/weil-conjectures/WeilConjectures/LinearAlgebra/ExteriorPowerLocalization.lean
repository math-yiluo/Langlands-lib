/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.LinearAlgebra.GenericExteriorPowerLocalization

/-! # Localization of exterior powers

Source: the localization argument of
`new-q1-exterior-sheaf-affine-unit-bijective`, step 2, using the alternating
universal property of exterior powers (Stacks Project, Algebra, Section 00DM).
(blueprint: new-v2-exterior-power-localization). -/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory

namespace exteriorPower

/-- A map of exterior powers characterized on pure wedges preserves localization.
This is the `ModuleCat` form of `isLocalizedModule_of_pure_wedge`.
Source: Stacks Project, Algebra, Section 00DM; the fraction construction in step 2
of `new-q1-exterior-sheaf-affine-unit-bijective`.
(blueprint: new-v2-exterior-power-localization).

Proof: view `N` and `⋀^n_B N` as `R`-modules by restriction of scalars along `R → B`;
these actions form scalar towers, so `isLocalizedModule_of_pure_wedge` applies. -/
theorem isLocalizedModule_of_wedge
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (S : Submonoid R) [IsLocalization S B]
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} B)
    (f : M ⟶ (ModuleCat.restrictScalars (algebraMap R B)).obj N)
    [IsLocalizedModule S f.hom] (n : ℕ)
    (g : ModuleCat.of R (⋀[R]^n M) ⟶
      (ModuleCat.restrictScalars (algebraMap R B)).obj (ModuleCat.of B (⋀[B]^n N)))
    (hg : ∀ a : Fin n → M,
      g (ιMulti R n a) = ιMulti B n (fun i ↦ f (a i))) :
    IsLocalizedModule S g.hom := by
  let : Module R N := ((ModuleCat.restrictScalars (algebraMap R B)).obj N).isModule
  let : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let fR : M →ₗ[R] N := f.hom
  let : IsLocalizedModule S fR := inferInstanceAs (IsLocalizedModule S f.hom)
  exact isLocalizedModule_of_pure_wedge S fR n g.hom hg

end exteriorPower

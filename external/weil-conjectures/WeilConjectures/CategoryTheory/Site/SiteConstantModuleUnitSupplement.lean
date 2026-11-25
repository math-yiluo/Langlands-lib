/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.CategoryTheory.SiteConstantModuleUnit

/-! # The constant-module sheafification unit

Source: Stacks Project, Modules on Sites, Tags 03CY and 093T.
(blueprint: lem-sf-constant-module-unit-locally-bijective).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

instance (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallyInjective J (siteConstantModuleUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (toSheafify J ((siteConstantModulePresheaf (C := C) Λ).obj M).presheaf))

instance (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallySurjective J (siteConstantModuleUnit J Λ M) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (toSheafify J ((siteConstantModulePresheaf (C := C) Λ).obj M).presheaf))

instance (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallyInjective J (siteConstantModuleUnitSections J Λ M) where
  equalizerSieve_mem {U} x y h := by
    exact Presheaf.equalizerSieve_mem J (siteConstantModuleUnit J Λ M) x y h

instance (M : ModuleCat.{u} Λ) :
    Presheaf.IsLocallySurjective J (siteConstantModuleUnitSections J Λ M) where
  imageSieve_mem {U} x := by
    exact Presheaf.imageSieve_mem J (siteConstantModuleUnit J Λ M) x

end CategoryTheory

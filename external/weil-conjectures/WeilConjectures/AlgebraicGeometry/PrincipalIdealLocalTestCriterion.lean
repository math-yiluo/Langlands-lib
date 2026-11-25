/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.SitePerfectModelRestriction
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowers
import WeilConjectures.CategoryTheory.UnitPowerCompleteness
/-! # The principal image ideal and the covering-sieve local tests

Source: Stacks 0999, 099B and 03DA.
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "R" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
set_option hygiene false in
local notation "A" => SheafOfModules.{u} R

variable [HasDerivedCategory.{w} A]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u} ((R).over U))]

/-- Use the given derived-category instances for the same slice module categories. Composing a
restricted commutative ring sheaf with forgetful coefficients agrees definitionally with
restricting its ring sheaf.

Source: Stacks 0999, 099B and 03DA.
(auxiliary; not a blueprint node). -/
abbrev principalLocalTestSliceDerived :
    ∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))) :=
  fun U ↦ inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} ((R).over U)))

end CategoryTheory

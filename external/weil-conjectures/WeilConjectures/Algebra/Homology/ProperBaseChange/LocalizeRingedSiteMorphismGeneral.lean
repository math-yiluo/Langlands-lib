/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.Localized.LocalizedSheavesOverRepresentable
import WeilConjectures.CategoryTheory.Localized.LocalizedSetPullbackComparison
import WeilConjectures.CategoryTheory.Localized.LocalizedCommRingPullbackComparison
import WeilConjectures.Algebra.Homology.ProperBaseChange.LocalizedModulePullbackComparison

/-!
# Localization of ringed-site morphisms without extra covering axioms

Source: Stacks Project, Modules on Sites, Tag 04J0; Sites, Tag 03CF
(blueprint: lem-weil-pbc-localize-ringed-site-morphism).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S)

end SheafOfModules

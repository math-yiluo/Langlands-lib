/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.Localized.LocalizedSetPullbackComparison
import WeilConjectures.Algebra.Homology.SliceModuleSheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Lifting.Left
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # The canonical module comparison for localization of a ringed site

Source: Stacks Project, Modules on Sites, Tag 04J0.
(blueprint: lem-weil-pbc-slice-module-pullback-isIso).
-/

@[expose] public noncomputable section

set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.TwoSquare
namespace CategoryTheory
section ChangeLeft
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : E ⥤ F} {R₂ : F ⥤ E}
  (a₁ : L₁ ⊣ R₁) (a₁' : L₁' ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₂' : L₂' ⊣ R₂)
  {G : C ⥤ E} {H : D ⥤ F} (b : TwoSquare R₁ H G R₂)
end ChangeLeft

section FreePresentation
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Abelian D]
  {F : C ⥤ D} {U : D ⥤ C} (adj : F ⊣ U) [U.Faithful]
  {L L' : D ⥤ E} (t : L ⟶ L') [PreservesColimitsOfShape WalkingParallelPair L]
  [PreservesColimitsOfShape WalkingParallelPair L']
  (h : ∀ X : C, IsIso (t.app (F.obj X)))
end FreePresentation
end CategoryTheory

namespace SheafOfModules
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
private abbrev sets (R : Sheaf J RingCat.{u}) :=
  toSheaf R ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})
end SheafOfModules

namespace SheafOfModules
variable {D C : Type u} [SmallCategory D] [SmallCategory C]
  {K : GrothendieckTopology D} {J : GrothendieckTopology C}
  (u : D ⥤ C) [u.IsContinuous K J]
  {R : Sheaf K RingCat.{u}} {S : Sheaf J RingCat.{u}}
  (a : R ⟶ (u.sheafPushforwardContinuous RingCat.{u} K J).obj S)

end SheafOfModules

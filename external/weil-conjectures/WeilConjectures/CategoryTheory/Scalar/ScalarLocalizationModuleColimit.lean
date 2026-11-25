/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationCoefficientActions
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement

/-!
# Scalar localization as an ordinary module-sheaf colimit

Source: Stacks Project, Tags 00CM, 03CY and 03EK.
(blueprint: lem-weil-pbc-scalar-localization-module-colimit)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

attribute [local irreducible] CategoryTheory.scalarLocalizationCoefficientMap
  SheafOfModules.tensorPresheafUnit SheafOfModules.regularTensorIso
  SheafOfModules.tensorObjIsoSheafification
  CategoryTheory.ringedLocalizationRing CategoryTheory.ringedLocalizationRingUnit

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

end CategoryTheory

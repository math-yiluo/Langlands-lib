/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
import WeilConjectures.CategoryTheory.Ringed.RingedProjectionFormulaResolutionNaturality
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral

/-! Naturality of the mixed tensor representative. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

end SheafOfModules

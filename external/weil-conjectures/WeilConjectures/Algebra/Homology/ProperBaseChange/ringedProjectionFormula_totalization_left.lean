/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
import WeilConjectures.Algebra.Homology.Ringed.RingedProjectionFormulaMixedComparison
import WeilConjectures.Algebra.Homology.Ringed.RingedProjectionFormulaMixedNaturality

/-! The left inverse equation for the signed totalization projection formula. -/

@[expose] public section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
-- The counit calculation keeps the signed total-complex representatives explicit.
end SheafOfModules

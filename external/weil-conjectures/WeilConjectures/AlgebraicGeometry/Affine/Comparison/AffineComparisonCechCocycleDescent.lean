/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonEtaleCechPresentation
import WeilConjectures.AlgebraicGeometry.AffineEtaleCechSystem.AffineComparisonCechSystemSections
import WeilConjectures.CategoryTheory.Sites.ProperBaseChange.OrderedCechUliftComparison

/-!
# Descent of finite affine comparison Čech cocycles

Source: Stacks Project, Tag 099U, the two finite Čech limit reductions in condition (3).
(blueprint: lem-cbc-affine-comparison-cech-cocycle-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

end AlgebraicGeometry.ProEtale

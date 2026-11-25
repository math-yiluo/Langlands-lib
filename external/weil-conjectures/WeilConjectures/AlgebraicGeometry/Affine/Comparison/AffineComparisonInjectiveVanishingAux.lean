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

import WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonCechCocycleDescent
import WeilConjectures.CategoryTheory.InjectiveSheafCechAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.CategoryTheory.FinitePrecoverage
import WeilConjectures.CategoryTheory.ArrowsFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonPullbackSections
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Finite affine Čech exactness for comparison pullbacks of injectives

Source: Stacks Project, Tag 099U, verification of condition (3).
(blueprint: lem-cbc-abelian-affine-comparison-vanishing-aux).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

end AlgebraicGeometry.ProEtale

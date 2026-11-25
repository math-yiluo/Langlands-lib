/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived

import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionComparisonExists
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleResolutionHomologyIndependent

/-! # Resolution representation of canonical cohomology comparison

Source: Stacks Project, Tags 072W and 0733(1).
(blueprint: lem-weil-pbc-zariski-etale-resolution-map)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

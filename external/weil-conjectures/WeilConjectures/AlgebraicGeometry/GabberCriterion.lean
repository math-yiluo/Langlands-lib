/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.EtaleMayerVietoris
import WeilConjectures.AlgebraicGeometry.ZariskiCohomologyLocallyZero
import WeilConjectures.AlgebraicGeometry.StrictHenselianZariskiEtaleComparison
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.GabberCriterionDegree

/-!
# Gabber's criterion for vanishing of higher etale cohomology

Source: Stacks Project, Etale Cohomology, Lemma 0GY0, label `lemma-gabber-criterion`
(blueprint: lem-weil-pbc-gabber-criterion).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor

/-!
# Pullback from the pro-étale point

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-pullback-from-point/_section.md (blueprint: sk-def-sfb-pullback-from-point).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite

namespace AlgebraicGeometry.ProEtale

/-- The inverse image from the pro-étale point to a scheme.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-pullback-from-point/_section.md, parts 2--4
  (blueprint: sk-def-sfb-pullback-from-point).
-/
noncomputable abbrev sfbPullbackFromPoint (X : Scheme.{u}) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⥤
      Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  upperStarFromPoint X

/-- The direct image corresponding to the inverse image from the point.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-def-sfb-pullback-from-point/_section.md, parts 3--4
  (blueprint: sk-def-sfb-pullback-from-point).
-/
noncomputable abbrev sfbPullbackFromPointRightAdjoint (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  ProEtale.lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar

end AlgebraicGeometry.ProEtale

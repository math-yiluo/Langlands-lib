/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceExists

/-!
# Restriction and trace for finite étale morphisms

Source: Stacks Project, Section 03SH, Definition 03SE and the characterization following it
(blueprint: def-weil-pbc-finite-etale-trace).

## Main definitions

* `finiteEtaleRestriction`: the unit of inverse image adjoint to direct image.
* `finiteEtaleTrace`: the component of the unique characterized trace family.

For a sheaf of `ℤ/n`-modules, these definitions are applied to its underlying abelian sheaf.
Inverse and direct image are additive, so they preserve annihilation by `n`. Every additive
map between groups killed by `n` is `ℤ/n`-linear for their unique `ℤ/n`-module structures;
thus the same maps are used with these coefficients, including `n = 1`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Restriction is the unit at `F` of `f⁻¹ ⊣ f_*`. Source: Stacks Project, Section 03SH,
first paragraph (blueprint: def-weil-pbc-finite-etale-trace).

Construction step 1: use the adjunction of def-weil-pbc-inverse-image with the direct
image of def-weil-pbc-direct-image and evaluate its unit at `F`. -/
noncomputable def finiteEtaleRestriction {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    F ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj F) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F

/-- Trace is the member at `(f, F)` of the unique family given by
`existsUnique_finiteEtaleTrace`. That family is natural in `F`, commutes with étale
localization, and is the sum map for every finite split covering, including the empty one.
The definition selects data from the named existence theorem, rather than postponing data.
Source: Stacks Project, Definition 03SE and the following characterization in Section 03SH
(blueprint: def-weil-pbc-finite-etale-trace).

Construction steps 2 and 3: Stacks permits using the localization and split-sum
characterization without constructing `f_!`. Choose the entire family supplied by
lem-weil-pbc-finite-etale-trace-exists, then evaluate at `(f, F)`. Uniqueness of that
family makes the result independent of the choice, including local trivializations.
Construction step 4: for coefficients `ℤ/n`, use the underlying abelian sheaf of
def-weil-pbc-etale-sheaves. Additivity of inverse and direct image preserves
`n • 𝟙 = 0`; hence their sections are killed by `n`, and every component of restriction
and trace is `ℤ/n`-linear because it is an additive homomorphism. -/
noncomputable def finiteEtaleTrace {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsFinite f] [Etale f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj F) ⟶ F :=
  Classical.choose existsUnique_finiteEtaleTrace.exists X Y f inferInstance inferInstance F

end AlgebraicGeometry.Etale

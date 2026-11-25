/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Units congruent to one modulo a power of the nilradical

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: def-sc-reduction-units-power-kernel)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The j-th nilpotent-units sheaf on X is the kernel of restriction of units to the
closed subscheme cut out by the (j+1)-st power of the nilradical. On an etale affine
object it consists of units congruent to one modulo the pulled-back ideal power.
This is a kernel construction, independent of any existence theorem for filtrations.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: def-sc-reduction-units-power-kernel) -/
noncomputable def reductionUnitsPowerKernel (X : Scheme.{u}) (j : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (gmSheafToLowerStarGmSheaf (X.nilradical ^ (j + 1)).subschemeι)

end AlgebraicGeometry.Scheme

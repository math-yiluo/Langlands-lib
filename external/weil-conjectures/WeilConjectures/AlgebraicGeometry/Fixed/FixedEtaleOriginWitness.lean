/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# Retained etale-origin witnesses in fixed-module coordinates

Source: blueprint proposition-proper-direct-image-constructible-complexes--5, displayed pair
(L,alpha), Stacks Tag 099R (blueprint: proposition-proper-direct-image-constructible-complexes--5).

The ringed witness remains imported. This is the same pair in the ordinary fixed-scalar
presentation used by the closed-support and comparison-class adjunctions.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A specified bounded-below etale antecedent and the specified comparison isomorphism.
The target is already in D+; no constructibility or chosen preimage is imposed.
Source: blueprint proposition-proper-direct-image-constructible-complexes--5, displayed pair
(L,alpha), Stacks Tag 099R (blueprint:
proposition-proper-direct-image-constructible-complexes--5). -/
structure FixedEtaleOriginWitness (T : Scheme.{u}) (A : Type (u + 1))
    [Ring A]
    (K : DerivedCategory.Plus (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))) where
  /-- The retained bounded-below antecedent. -/
  complex : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
  /-- Its specified ordinary derived comparison isomorphism. -/
  iso : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
    complex.obj ≅ K.obj

end AlgebraicGeometry.Scheme

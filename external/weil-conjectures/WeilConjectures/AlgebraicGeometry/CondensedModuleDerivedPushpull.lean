/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

/-!
# The total derived module-object pushforward and pullback

(blueprint: sk-def-sfb-module-derived-pushpull).

These are the general derived functors of the full underived composites. Naming their
specializations once shares the structural arguments in concrete coefficient statements.
The published derived adjunction, bounded-below version and resolution comparisons remain
publicly imported; no construction or choice of derived functors is replaced.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The total right derived functor of the full restriction-of-scalars pushforward.
This is exactly `Functor.rightDerivedFunctor (lowerStar Λ f)`, computed on K-injectives.
Source: blueprint sk-def-sfb-module-derived-pushpull, first displayed formula
(blueprint: sk-def-sfb-module-derived-pushpull). -/
def moduleObjectDerivedPushforward :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) :=
  (lowerStar Λ f).rightDerivedFunctor

/-- The total left derived functor of the full extension-of-scalars pullback.
This is exactly `Functor.leftDerivedFunctor (upperStar Λ f)`, computed on K-flat objects.
Source: blueprint sk-def-sfb-module-derived-pushpull, second displayed formula
(blueprint: sk-def-sfb-module-derived-pushpull). -/
def moduleObjectDerivedPullback :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (upperStar Λ f).leftDerivedFunctor

end AlgebraicGeometry.ProEtale.CondensedRing

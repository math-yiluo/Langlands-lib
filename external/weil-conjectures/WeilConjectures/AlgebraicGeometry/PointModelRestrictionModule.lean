/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData

/-! # Typed constructions for discrete point models

These are the existing constructions, with their module categories recorded in the type.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- Restriction of the given internal module along a composite scheme morphism.
Source: Stacks Tag 00YV and the integral-models local-model step
(auxiliary; not a blueprint node).
This is the existing inverse image evaluated on N. Its codomain is recorded explicitly,
so its consumers need not unfold the inverse-image construction to recover that category. -/
def pointModelRestriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : Y ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (g : Z ⟶ Y) :
    Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) :=
  (CondensedRing.upperStar Λ (g ≫ f)).obj N

end AlgebraicGeometry.ProEtale.IntegralModelsStacks

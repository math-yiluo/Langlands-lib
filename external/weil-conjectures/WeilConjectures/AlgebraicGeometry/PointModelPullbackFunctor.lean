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

/-- The actual point pullback on modules, with its codomain category fixed.
Source: Stacks Tag 00YV and the integral-models local-model step
(auxiliary; not a blueprint node).
The functor is the existing mapMod of upperStarFromPoint; both its object and morphism
maps are those of that functor. No equivalence or preservation property is assumed here. -/
def pointModelPullbackFunctor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) :=
  (upperStarFromPoint Z).mapMod Λ

end AlgebraicGeometry.ProEtale.IntegralModelsStacks

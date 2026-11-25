/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionInflation
public import WeilConjectures.CategoryTheory.InternalActionSite.InternalActionSitePresentation
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Grothendieck structure and exact restriction of internal sheaf actions

Source: main-20261015, sk-thm-sf-ctf-stability-direct-images, paragraph (3),
agent-formulated categorical input
(blueprint: lem-sfb-sheaf-action-grothendieck-inflation).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InternalActionSite

variable {C : Type u} [SmallCategory C]
  {K L : Cᵒᵖ ⥤ GrpCat.{u}} {R : Cᵒᵖ ⥤ RingCat.{u}}

private theorem forget_additive (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u}) :
    (forgetSheaf (K := K) J S).Additive where
  map_add := by intros; rfl

private theorem forget_faithful (J : GrothendieckTopology C) (S : Sheaf J RingCat.{u}) :
    (forgetSheaf (K := K) J S).Faithful where
  map_injective := by
    intro M N f g h
    apply ObjectProperty.hom_ext
    apply Subtype.ext
    exact congrArg SheafOfModules.Hom.val h

@[instance_reducible]
private noncomputable def actionAbelian [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) (P : Presentation K J hJ S) :
    Abelian (EquivariantSheaf (K := K) J.toGrothendieck
      (baseRing J.toGrothendieck S)) := by
  let E := P.sheafEquivalence
  have : HasFiniteProducts (EquivariantSheaf (K := K) J.toGrothendieck
      (baseRing J.toGrothendieck S)) :=
    ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E.functor⟩
  exact abelianOfEquivalence E.functor

end CategoryTheory.InternalActionSite

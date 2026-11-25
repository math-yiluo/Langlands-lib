/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpFull
import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrpEssSurj

@[expose] public section

universe u w
open CategoryTheory
namespace Rep

attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

/--
Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-exc-discrete-continuous-rep-commgrp-compatible).

Proof: Given a commutative internal group object, transport its multiplication,
unit, and inverse along Cartesian comparison maps to obtain an abelian group on the
carrier; equivariance makes the action linear and continuity gives open stabilizers.
Conversely, use the additive and integer-module operations of a discrete continuous
representation to form the internal group object. On morphisms both constructions
use the underlying equivariant map, and the carrier comparisons commute with every
such map.

This is the objectwise construction needed for the equivalence: from a commutative
internal group object one constructs the integer module structure on its carrier,
and conversely; the construction also supplies chosen carrier isomorphisms and
checks their compatibility with every equivariant morphism.  The construction is
left as a separate theorem so that the categorical natural-isomorphism assembly
below is a short formal step.
-/
theorem discreteContinuousRep_equiv_with_compatible_objectwise_iso
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    let D := DiscreteContinuousRep.{0, u, w} ℤ G
    let U : D ⥤ Rep.{w} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
    ∃ E : CommGrp (DiscreteContAction (Type w) G) ≌ D,
      ∃ e : ∀ X, (E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
        (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G).obj X ≅
          (CommGrp.forget (DiscreteContAction (Type w) G) ⋙ V).obj X,
      ∀ {X Y} (f : X ⟶ Y),
        ((E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
          (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G).map f) ≫
            (e Y).hom = (e X).hom ≫
              ((CommGrp.forget (DiscreteContAction (Type w) G) ⋙ V).map f) := by
  dsimp
  let H := discreteContinuousRepToCommGrp (G := G)
  let := discreteContinuousRepToCommGrp_full G
  let := discreteContinuousRepToCommGrp_essSurj G
  let : H.IsEquivalence := {}
  let E := H.asEquivalence
  let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G)) ⋙
    ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
  let W := CommGrp.forget (DiscreteContAction (Type w) G) ⋙ V
  let e := Functor.isoWhiskerRight E.counitIso W
  refine ⟨E.symm, fun X ↦ e.app X, ?_⟩
  intro X Y f
  exact e.hom.naturality f

end Rep

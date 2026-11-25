/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
import WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrpAux

/-!
# Commutative group objects in discrete continuous actions

Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-exc-discrete-continuous-rep-commgrp)
-/

@[expose] public section

universe u w

open CategoryTheory

namespace Rep

attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

/-- Source: Stacks Project, Tag 04JQ, proof of
`lemma-equivalence-abelian-sheaves-point`.
(blueprint: lem-exc-discrete-continuous-rep-commgrp).

Proof: A commutative group object in discrete continuous G-sets gives an abelian
law on its carrier: interpret its product as the Cartesian product via the
unique product comparison, and its unit as the singleton. The internal group
identities then give the abelian group identities on elements. Give this abelian
group its canonical integer module structure. Equivariance of the group law
and unit makes each action map additive, hence integer-linear. The inverse
group element gives its inverse. Joint continuity on a discrete carrier implies
open stabilizers: the orbit map at x is continuous, so the inverse image of {x}
is open. This gives a discrete continuous integer representation.
Conversely, for a representation with open stabilizers put the discrete topology
on its carrier. Its action is jointly continuous: at (g,x) the open set g times
the stabilizer of x, paired with the singleton {x}, maps constantly to g x.
The abelian operations are equivariant and therefore are morphisms of continuous
G-sets; the group identities give a commutative group object. On morphisms both
constructions retain the underlying equivariant map; preserving the group law
is equivalent to additivity, hence to integer-linearity. Recovering the original
operations gives the unit and counit, whose underlying maps are identity maps.
They are natural because morphisms retain their underlying maps. The underlying
action comparison is consequently natural. Any choice of Cartesian products
is allowed, since their unique comparison isomorphisms transport these laws.
The zero group, trivial group, and non-Hausdorff topological groups are included. -/
theorem discreteContinuousRep_commGrp
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    let D := DiscreteContinuousRep.{0, u, w} ℤ G
    let U : D ⥤ Rep.{w} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
    ∃ E : CommGrp (DiscreteContAction (Type w) G) ≌ D,
      Nonempty (E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
        (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G ≅
          CommGrp.forget _ ⋙ V) := by
  dsimp
  obtain ⟨E, ⟨e, he⟩⟩ :=
    discreteContinuousRep_equiv_with_compatible_objectwise_iso G
  refine ⟨E, ⟨NatIso.ofComponents e he⟩⟩

end Rep

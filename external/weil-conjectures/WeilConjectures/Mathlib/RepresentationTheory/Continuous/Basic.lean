/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Finite continuous representations of a topological group

A representation of a topological group on a finite module is continuous for the discrete
topology on the module exactly when every stabilizer is open. This is the condition appearing
on the representation side of the Galois correspondence for finite local systems.

## Implementation notes

Mathlib has two notions of continuous representation: `ContRepresentation R G V`, a monoid
homomorphism `G →* V →L[R] V` for a topological module `V`, and the category `TopRep k G`,
equivalent to `Action (TopModuleCat k) G`. Both carry the topology of the module as data,
whereas here it is always the discrete topology of a *finite* module, and what is wanted is a
full subcategory of the abelian category `Rep Λ G` — the target of the Galois correspondence
has to be abelian for the correspondence to be an equivalence of abelian categories.
`Rep.IsFiniteContinuous` therefore spells out continuity for the discrete topology directly,
as the openness of every stabilizer.

## Main definitions

- `Rep.IsFiniteContinuous`
-/

@[expose] public section

universe v w

namespace Rep

/-- Blueprint `proposition-lattices-representations-normal-scheme`: Galois correspondence for finite
local systems.

A representation of a topological group `G` on a `Λ`-module is *finite continuous* if the
underlying module is finite and every stabilizer is open, i.e. the action is continuous for
the discrete topology on the module. For a profinite `G` this is exactly the condition
appearing in the Galois correspondence: a finite `Λ`-module with a continuous `G`-action. -/
def IsFiniteContinuous {Λ : Type v} [CommRing Λ] {G : Type w} [Group G] [TopologicalSpace G] :
    CategoryTheory.ObjectProperty (Rep.{v} Λ G) :=
  fun X ↦ Finite X.V ∧ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x}

end Rep

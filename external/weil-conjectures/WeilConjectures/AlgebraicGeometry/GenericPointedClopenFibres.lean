/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.GenericPointedClopenFibresCore

/-!
# Persistence of connected fibres of a pointed clopen piece

Source: Stacks Project, Tag 055N, proof, applying Tags 04KV and 055G.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A clopen piece with connected generic fibre containing the rational section point
has preconnected fibres after shrinking. No equality with a section component is asserted.

Source: Stacks Project, Tag 055N, the passage from a clopen generic component to
geometrically connected fibres, using Tags 04KV and 055G.
Proof: base change to the reduced closed subscheme on the closure of y, and restrict
the base to V. The displayed clopen subset determines an open and closed subscheme.
Its inclusion is quasi-compact because its trace in every quasi-compact open is closed
and hence quasi-compact. Thus its morphism to the restricted integral base is finite
type. Its generic fibre is preconnected and contains the rational point supplied by
sigma, so it is nonempty and connected. The section at the generic point factors
through this open subscheme. Tag 04KV makes this generic fibre geometrically connected.
Tag 055G gives a nonempty open of the integral base on which all its fibres are
geometrically connected. Such an open contains y. Represent it by an ambient open W
and intersect W with V to ensure W is a subset of V. The closed-base-change and fibre
homeomorphisms identify each fibre with the set g inverse image {t} intersect A.
Geometric connectedness implies its topological preconnectedness. Empty fibres are
allowed by the conclusion, and no assertion is made outside the closure of y.

(blueprint: lem-sbc-generic-pointed-clopen-fibres) -/
theorem exists_open_preconnected_fibres_of_pointed_clopen {P T : Scheme.{u}}
    (g : P ⟶ T) [LocallyOfFiniteType g] [QuasiCompact g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (y : T) (V : Set T) (A : Set P)
    (hV : IsOpen V) (hyV : y ∈ V)
    (hA : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hconn : IsPreconnected (g ⁻¹' {y} ∩ A)) (hpoint : σ y ∈ A) :
    ∃ W : Set T, IsOpen W ∧ y ∈ W ∧ W ⊆ V ∧
      ∀ t ∈ W ∩ closure {y}, IsPreconnected (g ⁻¹' {t} ∩ A) := by
  obtain ⟨U, hU, hyU, hUf⟩ :=
    exists_open_preconnected_fibres_of_pointed_clopen_core g σ hσ y V A hV hyV hA hconn hpoint
  refine ⟨U ∩ V, hU.inter hV, ⟨hyU, hyV⟩, (fun _ h ↦ h.2), ?_⟩
  intro t ht
  exact hUf t ⟨ht.1.1, ht.2⟩

end AlgebraicGeometry

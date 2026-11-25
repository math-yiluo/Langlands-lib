/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.FlatFibreDimensionStrata

/-! # FlatFibreComponentDimensionSpecialization

Source: Stacks Project, Tag 054U (lemma-dimension-fibre-specialization).
(blueprint: lem-sbc-flat-fibre-component-dimension-specialization)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A component point admits a neighbourhood on which the fibre dimension is constant.
Source: Stacks Project, Tag 054T, the fibrewise dimension theorem used in Tag 054U.
The proof restricts to the open base and applies the constructible constancy theorem
for flat morphisms locally of finite presentation at a generic point of a fibre
component, then transports the resulting open through the fibre identification.
(blueprint: lem-sbc-flat-fibre-component-dimension-specialization-open) -/
theorem exists_fibre_dimension_open_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x : X) (hx : f x ∈ U)
    (hcomponent : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    ∃ V : X.Opens, x ∈ V ∧
      ∀ y ∈ V, topologicalKrullDimAt (f.asFiber y) =
        topologicalKrullDimAt (f.asFiber x) := by
  obtain ⟨V, hcover, hdim⟩ := exists_fibre_dimension_strata_of_flat_restrict f U
  obtain ⟨n, hxn⟩ := hcover x hx hcomponent
  refine ⟨V n, hxn, ?_⟩
  intro y hy
  exact (hdim n y hy).trans (hdim n x hxn).symm

/-- Local fibre dimension is constant along a generalization of a fibre component point.
Source: Stacks Project, Tag 054U (lemma-dimension-fibre-specialization).
Proof: restrict the base to U and the source to its inverse image. The original fibres
at images of x and x' are canonically isomorphic to the restricted fibres; these
isomorphisms preserve component generic points and local dimension. Specialization
is unchanged by passing to an open subspace. For the flat locally finitely presented
restricted morphism, Tag 054T gives an open neighbourhood of a component generic
point on which local fibre dimension is constant. Every generalization belongs to
this open neighbourhood, so the two dimensions agree. Transport back along the fibre
isomorphisms. No irreducibility assumption on the base is necessary.
(blueprint: lem-sbc-flat-fibre-component-dimension-specialization) -/
theorem fibre_dimension_eq_of_specializes_component_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x x' : X) (hx : f x ∈ U) (hsp : x' ⤳ x)
    (hcomponent : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    topologicalKrullDimAt (f.asFiber x') = topologicalKrullDimAt (f.asFiber x) := by
  obtain ⟨V, hxV, hV⟩ := exists_fibre_dimension_open_of_flat_restrict
    f U x hx hcomponent
  exact hV x' (hsp.mem_open V.isOpen hxV)

end AlgebraicGeometry

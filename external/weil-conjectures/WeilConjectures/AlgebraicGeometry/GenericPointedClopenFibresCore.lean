/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.PointedClopenIntegralModel
import WeilConjectures.AlgebraicGeometry.GenericGeometricallyConnectedSpread
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! Core geometric spreading statement for pointed clopen fibres.

Source: Stacks Project, Tag 055N, using Tags 04KV and 055G.
(blueprint: new-lem-sbc-generic-pointed-clopen-fibres-core)
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The geometric shrinking step produces an open neighbourhood of `y` on which the
preconnectedness conclusion holds; containment in a prescribed open is handled separately.

Source: Stacks Project, Tag 055N, passage from a pointed clopen generic fibre to connected
fibres, using Tags 04KV and 055G.
Proof: pass to the reduced closure of `y`, form the open and closed subscheme represented by
`A`, and apply generic connectedness of fibres to its geometrically connected generic fibre.
Transport the resulting open back to `T`; fibre homeomorphisms identify its fibres with
`g ⁻¹' {t} ∩ A`.

(blueprint: new-lem-sbc-generic-pointed-clopen-fibres-core) -/
theorem exists_open_preconnected_fibres_of_pointed_clopen_core {P T : Scheme.{u}}
    (g : P ⟶ T) [LocallyOfFiniteType g] [QuasiCompact g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (y : T) (V : Set T) (A : Set P)
    (hV : IsOpen V) (hyV : y ∈ V)
    (hA : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hconn : IsPreconnected (g ⁻¹' {y} ∩ A)) (hpoint : σ y ∈ A) :
    ∃ U : Set T, IsOpen U ∧ y ∈ U ∧
      ∀ t ∈ U ∩ closure {y}, IsPreconnected (g ⁻¹' {t} ∩ A) := by
  obtain ⟨S, X, hS, f, hft, hqc, j, hj, hη, e, r, hr⟩ :=
    exists_pointed_clopen_integral_model g σ hσ y V A hV hyV hA hpoint
  have hconn' : IsPreconnected (g ⁻¹' {(j (genericPoint S)).val} ∩ A) := by
    simpa only [hη] using hconn
  have : PreconnectedSpace ↥(g ⁻¹' {(j (genericPoint S)).val} ∩ A) :=
    isPreconnected_iff_preconnectedSpace.mp hconn'
  have : Nonempty ↥(g ⁻¹' {(j (genericPoint S)).val} ∩ A) :=
    ⟨e (genericPoint S) (r (Nonempty.some inferInstance))⟩
  have : ConnectedSpace ↥(g ⁻¹' {(j (genericPoint S)).val} ∩ A) := ⟨inferInstance⟩
  have : ConnectedSpace (f.fiber (genericPoint S)) :=
    (e (genericPoint S)).connectedSpace_iff.mpr inferInstance
  have hgeom := GeometricallyConnected.of_connectedSpace_of_section
    (f.fiberToSpecResidueField (genericPoint S)) r hr
  obtain ⟨W, hW, hηW, hWconn⟩ :=
    exists_open_geometricallyConnected_fibres_of_generic f hgeom
  obtain ⟨U, hU, hUW⟩ := isOpen_induced_iff.mp (hj.isOpenMap W hW)
  refine ⟨U, hU, ?_, ?_⟩
  · have : j (genericPoint S) ∈ j '' W := ⟨genericPoint S, hηW, rfl⟩
    rw [← hUW] at this
    simpa only [Set.mem_preimage, hη] using this
  · intro t ht
    have ht' : (⟨t, ht.2⟩ : closure {y}) ∈ j '' W := by
      rw [← hUW]
      exact ht.1
    obtain ⟨s, hs, hst⟩ := ht'
    have : GeometricallyConnected (f.fiberToSpecResidueField s) := hWconn s hs
    have : ConnectedSpace (f.fiber s) :=
      GeometricallyConnected.connectedSpace_of_subsingleton (f.fiberToSpecResidueField s)
    have : ConnectedSpace ↥(g ⁻¹' {(j s).val} ∩ A) :=
      (e s).connectedSpace_iff.mp inferInstance
    have hc : IsPreconnected (g ⁻¹' {(j s).val} ∩ A) :=
      isPreconnected_iff_preconnectedSpace.mpr inferInstance
    simpa only [hst] using hc

end AlgebraicGeometry

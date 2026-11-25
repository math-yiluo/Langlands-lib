/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! The generic fibre of a finite morphism lies in the interiors of a finite stratification. -/

@[expose] public section

set_option autoImplicit false
universe u

namespace AlgebraicGeometry.Scheme

/-- Every point of the generic fibre lies in the union of the interiors of the strata.
Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof paragraphs 1--3 of
`lem-weil-pbc-finite-pushforward-generic-constructible`.
(blueprint: lem-weil-pbc-finite-generic-fiber-stratum-interiors).

Proof: The finite source is Noetherian. Let C be an irreducible component
containing a point x of the generic fibre, and c its generic point. Continuity
makes g(c) specialize to the generic point of S, and that generic point specializes
to every point of S; since S is T0, g(c) is the generic point. A finite morphism has
discrete fibres, so c specializes to x within a discrete subspace and hence c = x.
Every irreducible component of a Noetherian space contains a nonempty open O of the
whole space (remove all the other finitely many components). The generic point x
lies in O. Choose the stratum T_i containing x. Its closure
contains C, and its coborder is open because the stratum is locally closed.
Thus O intersect coborder(T_i) is an open neighbourhood of x contained in T_i,
so x lies in the interior of that stratum and hence in W.
This works without reducing Z and covers the empty generic fibre vacuously. -/
theorem generic_fiber_subset_stratum_interiors
    (S : Scheme.{u}) [IsIntegral S] [IsNoetherian S] [IsAffine S]
    {Z : Scheme.{u}} (g : Z ⟶ S) [IsFinite g] (T : Stratification Z) :
    ∀ x : Z, g x = genericPoint S → x ∈ (T.interiorUnion : Set Z) := by
  classical
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  let : IsNoetherian Z := ⟨⟩
  intro x hx
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents x
  let c := hC.1.genericPoint
  have hc : IsGenericPoint c C :=
    hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  have hcx : c ⤳ x := hc.specializes mem_irreducibleComponent
  have hgc : g c = genericPoint S := by
    have h := hcx.map g.continuous
    rw [hx] at h
    exact (h.antisymm (genericPoint_specializes (g c))).eq
  have hceq : c = x := (g.isDiscrete_preimage_singleton (genericPoint S)).eq_of_specializes
    hcx hgc hx
  obtain ⟨O, hO, hOne, hOC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  have hcO : c ∈ O := (hc.mem_open_set_iff hO).mpr
    (by obtain ⟨y, hy⟩ := hOne; exact ⟨y, hOC hy, hy⟩)
  have hxO : x ∈ O := hceq ▸ hcO
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (T.iUnion_stratum_eq_univ ▸ Set.mem_univ x)
  have hCS : C ⊆ closure (T.stratum i) :=
    (hc.mem_closed_set_iff isClosed_closure).mp (hceq.symm ▸ subset_closure hxi)
  have hsub : O ∩ coborder (T.stratum i) ⊆ T.stratum i := by
    intro y hy
    have : y ∈ coborder (T.stratum i) ∩ closure (T.stratum i) := ⟨hy.2, hCS (hOC hy.1)⟩
    rwa [coborder_inter_closure] at this
  have hxin : x ∈ interior (T.stratum i) := by
    apply interior_mono hsub
    rw [(hO.inter (T.isLocallyClosed_stratum i).isOpen_coborder).interior_eq]
    exact ⟨hxO, subset_coborder hxi⟩
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hxin⟩

end AlgebraicGeometry.Scheme

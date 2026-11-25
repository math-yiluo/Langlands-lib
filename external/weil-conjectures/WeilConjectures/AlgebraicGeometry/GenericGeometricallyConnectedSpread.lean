/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.GenericFibreIncidenceSpread

/-!
# Spreading geometric connectedness of a generic fibre

Source: Stacks Project, Tag 055G (lemma-geometrically-connected-generic-fibre).
(blueprint: lem-sbc-generic-geometrically-connected-spread)
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

private theorem finite_closed_cover_paths {T : Type*} [TopologicalSpace T]
    [ConnectedSpace T] {I : Type*} [Finite I] (A : I → Set T)
    (hclosed : ∀ i, IsClosed (A i)) (hne : ∀ i, (A i).Nonempty)
    (hcover : (⋃ i, A i) = Set.univ) (i j : I) :
    Relation.ReflTransGen (fun a b => (A a ∩ A b).Nonempty) i j := by
  classical
  by_contra hij
  let R := fun a b : I => (A a ∩ A b).Nonempty
  let J : Set I := {k | Relation.ReflTransGen R i k}
  let U : Set T := ⋃ k ∈ J, A k
  let V : Set T := ⋃ k ∈ Jᶜ, A k
  have hU : IsClosed U := J.toFinite.isClosed_biUnion fun k _ => hclosed k
  have hV : IsClosed V := Jᶜ.toFinite.isClosed_biUnion fun k _ => hclosed k
  have hsplit : Set.univ ⊆ U ∪ V := by
    intro x _
    have hx : x ∈ ⋃ k, A k := hcover.symm ▸ Set.mem_univ x
    obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
    by_cases hk : k ∈ J
    · exact Or.inl (Set.mem_iUnion₂_of_mem hk hxk)
    · exact Or.inr (Set.mem_iUnion₂_of_mem hk hxk)
  obtain ⟨x, hx⟩ := hne i
  obtain ⟨y, hy⟩ := hne j
  have hi : i ∈ J := Relation.ReflTransGen.refl
  have hj : j ∈ Jᶜ := hij
  obtain ⟨z, _, hzU, hzV⟩ := isPreconnected_closed_iff.mp
    isConnected_univ.isPreconnected U V hU hV hsplit
    ⟨x, Set.mem_univ x, Set.mem_iUnion₂_of_mem hi hx⟩
    ⟨y, Set.mem_univ y, Set.mem_iUnion₂_of_mem hj hy⟩
  obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hzU
  obtain ⟨l, hl, hzl⟩ := Set.mem_iUnion₂.mp hzV
  exact hl (hk.tail ⟨z, hzk, hzl⟩)

/-- A finite type family with geometrically connected generic fibre has geometrically
connected fibres on an open neighbourhood of the generic point.

Source: Stacks Project, Tag 055G, lemma-geometrically-connected-generic-fibre.
Proof: after a finite extension of the generic field and shrinking the base, arrange
that the finitely many generic irreducible components are geometrically irreducible.
This change of base is open and surjective over an open, so geometric connectedness
of fibres descends. Reduce the base. Take closures of the generic components.
Shrink so these closures cover the total space and so pairs having empty generic
intersection are disjoint. Shrink again so every component has geometrically
irreducible fibres. For each pair with nonempty generic intersection, generic
flatness makes that intersection flat and finitely presented after further
shrinking; its image is then open and contains the generic point. Intersect these
finitely many images. The graph of nonempty intersections of the generic components
is connected because the generic fibre is connected. On the resulting open, after
any separably closed field extension each component is irreducible and this same
connected graph of intersections persists. Their union is therefore connected.
Descent returns a nonempty open in the original base, which contains its generic
point by irreducibility. The argument also covers a single generic component.

(blueprint: lem-sbc-generic-geometrically-connected-spread) -/
theorem exists_open_geometricallyConnected_fibres_of_generic {X S : Scheme.{u}}
    [IrreducibleSpace S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (hη : GeometricallyConnected (f.fiberToSpecResidueField (genericPoint S))) :
    ∃ W : Set S, IsOpen W ∧ genericPoint S ∈ W ∧
      ∀ s ∈ W, GeometricallyConnected (f.fiberToSpecResidueField s) := by
  classical
  obtain ⟨L, instL, yη, I, instI, A, W, hclosed, hirr, hcover, hW, hηW, hspread⟩ :=
    exists_open_generic_fibre_incidence_spread f
  let : Field L := instL
  let : Finite I := instI
  have hgeneric : ConnectedSpace ↥(CategoryTheory.Limits.pullback
      (f.fiberToSpecResidueField (genericPoint S)) yη) :=
    pullback_of_geometrically
      ((geometricallyConnected_iff _).mp hη) L yη
  have hpaths := finite_closed_cover_paths A hclosed (fun i => (hirr i).nonempty) hcover
  have hn : Nonempty I := by
    obtain ⟨x⟩ := (inferInstance : Nonempty ↥(CategoryTheory.Limits.pullback
      (f.fiberToSpecResidueField (genericPoint S)) yη))
    have hx : x ∈ ⋃ i, A i := hcover.symm ▸ Set.mem_univ x
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
    exact ⟨i⟩
  refine ⟨W, hW, hηW, fun s hs => ?_⟩
  apply (geometricallyConnected_iff _).mpr
  apply (geometrically_iff_of_isClosedUnderIsomorphisms
    (P := fun Z : Scheme.{u} => ConnectedSpace ↥Z)).mpr
  intro K instK y
  obtain ⟨Z, p, B, hp, hB, hBcover, hedges⟩ := hspread s hs K instK y
  have hconnected : _root_.IsConnected (⋃ i, B i) :=
    _root_.IsConnected.iUnion_of_reflTransGen (fun i => (hB i).isConnected) fun i j =>
      Relation.ReflTransGen.mono hedges i j (hpaths i j)
  have : ConnectedSpace Z := connectedSpace_iff_univ.mpr (hBcover ▸ hconnected)
  exact hp.surj.connectedSpace p.continuous

end AlgebraicGeometry

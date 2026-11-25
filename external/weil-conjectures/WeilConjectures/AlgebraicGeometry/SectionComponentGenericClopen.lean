/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.GenericFibreComponentSpread
import WeilConjectures.AlgebraicGeometry.GenericPointedClopenFibres

/-!
# Generic clopenness of the component selected by a section

Source: Stacks Project, Tag 055N, using Tag 055M.
(blueprint: lem-sbc-section-component-generic-clopen)
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The section component is clopen over an open neighbourhood of a base point inside
its closure. The topology on the displayed subtype is the subspace topology.

Source: Stacks Project, Tag 055N, proof, using Tag 055M.
Proof: give the closure of y its reduced closed subscheme structure. Base change the
morphism and section to this integral scheme; Tag 055M identifies the section locus
with the inverse image of the original locus. The generic fibre is a finite type scheme
over a field, hence noetherian. Its section component and its complement are clopen.
Take their closures in the total space. Tag 054Y permits shrinking the integral base
so these two closures cover the total space; Tag 054W permits further shrinking to
make their intersection empty. The first closure is now clopen. Its generic fibre is
connected and has the rational point supplied by the section, so it is geometrically
connected by Tag 04KV. Tag 055G permits shrinking the base again so that all its fibres
are geometrically connected. Intersect also with the inverse image under the section
of the first closure; this open contains the generic point. Each fibre of the first
closure is then a nonempty connected clopen subset of the whole fibre containing the
section point, hence is precisely its connected component. This identifies the first
closure with the section locus on the remaining open. A closed immersion and its base
change are homeomorphisms onto their images, so the base-changed total space has the
subspace topology on the inverse image of the closure of y. Express the remaining open
of the closure of y as the intersection with an ambient open V of T. Since y is the
generic point of its closure, V contains y. Transport clopenness along the indicated
homeomorphism to obtain the displayed subtype statement.

(blueprint: lem-sbc-section-component-generic-clopen) -/
theorem exists_open_section_component_clopen {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (y : T) :
    ∃ V : Set T, IsOpen V ∧ y ∈ V ∧
      IsClopen {q : g ⁻¹' (V ∩ closure {y}) |
        (q : P) ∈ connectedComponentIn (g ⁻¹' {g (q : P)}) (σ (g (q : P)))} := by
  classical
  have hσ_apply (t : T) : g (σ t) = t := by
    rw [← Scheme.Hom.comp_apply, hσ]
    rfl
  obtain ⟨V, A, hV, hyV, hA, hgeneric⟩ :=
    exists_open_generic_fibre_component_spread g y (σ y) (hσ_apply y)
  have hpoint : σ y ∈ A := by
    have hmem := mem_connectedComponentIn (show σ y ∈ g ⁻¹' {y} from hσ_apply y)
    rw [← hgeneric] at hmem
    exact hmem.2
  have hconn : IsPreconnected (g ⁻¹' {y} ∩ A) := by
    rw [hgeneric]
    exact isPreconnected_connectedComponentIn
  obtain ⟨W, hW, hyW, hWV, hfibres⟩ :=
    exists_open_preconnected_fibres_of_pointed_clopen g σ hσ y V A hV hyV hA hconn hpoint
  let s : ↥(V ∩ closure {y}) → g ⁻¹' (V ∩ closure {y}) :=
    fun t ↦ ⟨σ t, by simpa only [Set.mem_preimage, hσ_apply] using t.2⟩
  have hs : Continuous s := (σ.continuous.comp continuous_subtype_val).subtype_mk _
  have hopen : IsOpen (s ⁻¹' {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A}) :=
    hA.isOpen.preimage hs
  obtain ⟨B, hB, hBeq⟩ := IsInducing.subtypeVal.isOpen_iff.mp hopen
  have hyB : y ∈ B := by
    have hy : (⟨y, hyV, subset_closure (Set.mem_singleton y)⟩ : ↥(V ∩ closure {y})) ∈
        s ⁻¹' {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A} := hpoint
    rw [← hBeq] at hy
    exact hy
  let L : Set T := W ∩ B
  have hLV : L ⊆ V := fun _ ht ↦ hWV ht.1
  let i : ↥(g ⁻¹' (L ∩ closure {y})) → g ⁻¹' (V ∩ closure {y}) :=
    fun q ↦ ⟨q.1, hLV q.2.1, q.2.2⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  have hAL : IsClopen {q : g ⁻¹' (L ∩ closure {y}) | (q : P) ∈ A} := hA.preimage hi
  refine ⟨L, hW.inter hB, ⟨hyW, hyB⟩, ?_⟩
  convert hAL using 1
  ext q
  let t : T := g (q : P)
  have ht : t ∈ L ∩ closure {y} := q.2
  have hσA : σ t ∈ A := by
    have hmem : (⟨t, hLV ht.1, ht.2⟩ : ↥(V ∩ closure {y})) ∈
        (Subtype.val ⁻¹' B) := ht.1.2
    rw [hBeq] at hmem
    exact hmem
  have hpre : IsPreconnected (g ⁻¹' {t} ∩ A) := hfibres t ⟨ht.1.1, ht.2⟩
  have hσF : σ t ∈ g ⁻¹' {t} := hσ_apply t
  let j : ↥(g ⁻¹' {t}) → g ⁻¹' (V ∩ closure {y}) :=
    fun r ↦ ⟨r.1, by
      have hr : g r.1 = t := r.2
      rw [Set.mem_preimage, hr]
      exact ⟨hLV ht.1, ht.2⟩⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hAF : IsClopen {r : g ⁻¹' {t} | (r : P) ∈ A} := hA.preimage hj
  have hsub : connectedComponent (⟨σ t, hσF⟩ : ↥(g ⁻¹' {t})) ⊆
      {r : g ⁻¹' {t} | (r : P) ∈ A} :=
    isPreconnected_connectedComponent.subset_isClopen hAF
      ⟨⟨σ t, hσF⟩, mem_connectedComponent, hσA⟩
  change ((q : P) ∈ connectedComponentIn (g ⁻¹' {t}) (σ t)) ↔ (q : P) ∈ A
  constructor
  · intro hq
    rw [connectedComponentIn_eq_image hσF] at hq
    obtain ⟨r, hr, hrq⟩ := hq
    exact hrq ▸ hsub hr
  · intro hq
    exact hpre.subset_connectedComponentIn ⟨hσF, hσA⟩ Set.inter_subset_left ⟨rfl, hq⟩

end AlgebraicGeometry

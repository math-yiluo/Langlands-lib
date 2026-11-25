/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Shrinking near a generic fibre

Source: Stacks Project, Tags 054Y and 054W.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A closed subset missing a fibre is absent over a neighbourhood in the closure
of its base point.

Source: Stacks Project, Tag 054W (Lemma 37.24.1), applied after the reduction to the
integral base in Tag 055N, proof, first two paragraphs.

Proof: give the closure of `y` its reduced closed subscheme structure `Z`. This is
integral with generic point over `y`. Base change `g` to `Z` and pull back the closed
set `C`. Give this pullback its reduced closed subscheme structure `W`. A closed
immersion is locally of finite type and quasi-compact, so `W → Z` is finite type.
Its generic fibre is empty by `hempty` and the homeomorphism from the scheme-theoretic
fibre onto the set-theoretic fibre. Tag 054W gives a nonempty open of `Z` over which
`W` is empty. Every nonempty open of the integral `Z` contains its generic point.
Represent this open as `V ∩ closure {y}` with `V` ambient open in `T`; then `y ∈ V`.
The base-change projection is a homeomorphism onto the inverse image of the closure
of `y`, so emptiness of `W` there is exactly the asserted disjointness. If `C` is
empty the conclusion holds with `V = Set.univ`.

(blueprint: lem-sbc-generic-fibre-closed-avoidance) -/
theorem exists_open_generic_fibre_closed_avoidance {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (C : Set P)
    (hC : IsClosed C) (hempty : g ⁻¹' {y} ∩ C = ∅) :
    ∃ V : Set T, IsOpen V ∧ y ∈ V ∧ Disjoint (g ⁻¹' (V ∩ closure {y})) C := by
  -- Alternative to the finite-type spreading argument above: Tag 02JQ supplies
  -- a specialization from the image of the closed subscheme supported on D.
  -- Mutual specialization then forces that image point to be y.
  let D : TopologicalSpace.Closeds P :=
    ⟨C ∩ g ⁻¹' closure {y}, hC.inter (isClosed_closure.preimage g.continuous)⟩
  let I := Scheme.IdealSheafData.vanishingIdeal D
  let j : I.subscheme ⟶ T := I.subschemeι ≫ g
  have hjD (x : I.subscheme) : I.subschemeι x ∈ (D : Set P) := by
    have hx : I.subschemeι x ∈ Set.range I.subschemeι := ⟨x, rfl⟩
    rw [I.range_subschemeι] at hx
    simpa [I] using hx
  have hy : y ∉ closure (Set.range j) := by
    intro hy
    obtain ⟨x, hx⟩ := exists_specializes_of_mem_closure_range j hy
    have hyx : y ⤳ j x := by
      rw [specializes_iff_mem_closure]
      simpa [j, Scheme.Hom.comp_apply] using (hjD x).2
    have he : j x = y := (hx.antisymm hyx).eq
    have hxempty : I.subschemeι x ∈ g ⁻¹' {y} ∩ C :=
      ⟨by simpa [j, Scheme.Hom.comp_apply] using he, (hjD x).1⟩
    rw [hempty] at hxempty
    exact hxempty
  refine ⟨(closure (Set.range j))ᶜ, isClosed_closure.isOpen_compl, hy, ?_⟩
  rw [Set.disjoint_left]
  intro x hx hxC
  have hxD : x ∈ (D : Set P) := ⟨hxC, hx.2⟩
  have hxI : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    simpa [I] using hxD
  obtain ⟨z, rfl⟩ := hxI
  exact hx.1 (subset_closure ⟨z, by simp [j]⟩)

end AlgebraicGeometry

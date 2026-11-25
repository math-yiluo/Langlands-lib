/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.GenericFlatness

/-! # Shrinking near a generic fibre

Source: Stacks Project, Tags 054Y and 054W.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- Two closed subsets covering a fibre cover the family over a neighbourhood in
its base point's closure.

Source: Stacks Project, Tag 054Y (Lemma 37.24.5), applied after the reduction to the
integral base in Tag 055N, proof, first two paragraphs.

Proof: give the closure of `y` its reduced induced closed subscheme structure Z,
using the vanishing ideal construction. Its inclusion j is a closed embedding,
and its range is the closure of y. This space is irreducible and the scheme is
reduced, so it is integral. The point η of Z over y specializes to every point of Z.
Base change g along j to a finite type morphism f. Generic flatness (Tag 052A)
gives a nonempty open U of Z on which f is flat. Since η specializes to every
point, U contains η. Express U as the inverse image of an ambient open V in T;
then V contains y. For x mapping into V intersected with the closure of y, lift
x to a point w of the pullback, whose image lies in U. Flatness lifts the
generalization from η to f(w), giving a point a over η specializing to w.
Projecting a to P gives a point of the original fibre over y, hence of C union D.
The projection of a specializes to x. Since C union D is closed, it contains x.
An empty generic fibre causes no exception: the same lifting argument shows
there can be no such x.

(blueprint: lem-sbc-generic-fibre-closed-cover-spread) -/
theorem exists_open_generic_fibre_closed_cover {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (C D : Set P)
    (hC : IsClosed C) (hD : IsClosed D) (hcover : g ⁻¹' {y} ⊆ C ∪ D) :
    ∃ V : Set T, IsOpen V ∧ y ∈ V ∧ g ⁻¹' (V ∩ closure {y}) ⊆ C ∪ D := by
  let J := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure {y}, isClosed_closure⟩ : TopologicalSpace.Closeds T)
  let Z := J.subscheme
  let j : Z ⟶ T := J.subschemeι
  have hr : Set.range j = closure {y} := by
    exact J.range_subschemeι.trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  have hZirr : IrreducibleSpace Z := by
    have hirr : IsIrreducible (Set.range j) := hr ▸ isIrreducible_singleton.closure
    have := Subtype.irreducibleSpace hirr
    have hu := (IrreducibleSpace.isIrreducible_univ (Set.range j)).image
      j.isEmbedding.toHomeomorph.symm
      j.isEmbedding.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ, j.isEmbedding.toHomeomorph.symm.surjective.range_eq] at hu
    exact (irreducibleSpace_def _).mpr hu
  have hZ : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  let η : Z := ⟨y, by
    change y ∈ closure {y}
    exact subset_closure (Set.mem_singleton y)⟩
  have hjη : j η = y := rfl
  have hη (z : Z) : η ⤳ z := by
    apply j.isEmbedding.specializes_iff.mp
    rw [hjη, specializes_iff_mem_closure]
    exact hr ▸ Set.mem_range_self z
  let f : Limits.pullback g j ⟶ Z := Limits.pullback.snd g j
  let p : Limits.pullback g j ⟶ P := Limits.pullback.fst g j
  obtain ⟨U, hU, hflat⟩ := exists_nonempty_open_flat_restrict f
  have hηU : η ∈ U := by
    obtain ⟨z, hz⟩ := hU
    exact (hη z).mem_open U.isOpen hz
  obtain ⟨V, hV, hVU⟩ := j.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
  refine ⟨V, hV, ?_, ?_⟩
  · have := hηU
    change η ∈ (U : Set Z) at this
    rw [← hVU] at this
    exact this
  · intro x hx
    obtain ⟨w, hw⟩ : x ∈ Set.range p := by
      rw [Scheme.Pullback.range_fst, hr]
      exact hx.2
    have hfw : f w ∈ U := by
      change f w ∈ (U : Set Z)
      rw [← hVU]
      change j (f w) ∈ V
      have he : j (f w) = g (p w) := by
        exact congrArg (fun k : Limits.pullback g j ⟶ T => k w)
          Limits.pullback.condition.symm
      rw [he, hw]
      exact hx.1
    let wU : (f ⁻¹ᵁ U).toScheme := ⟨w, hfw⟩
    let ηU : U.toScheme := ⟨η, hηU⟩
    have hs : ηU ⤳ (f ∣_ U) wU := by
      apply (subtype_specializes_iff _ _).mpr
      simpa only [morphismRestrict_base_coe] using hη (f w)
    obtain ⟨a, ha, hea⟩ := Flat.generalizingMap (f ∣_ U) hs
    have hfa : f a.1 = η := by
      simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hea
    have hpa : p a.1 ∈ g ⁻¹' {y} := by
      change g (p a.1) = y
      have he : g (p a.1) = j (f a.1) := by
        exact congrArg (fun k : Limits.pullback g j ⟶ T => k a.1)
          Limits.pullback.condition
      rw [he, hfa, hjη]
    have hspec : p a.1 ⤳ x := by
      rw [← hw]
      exact (ha.map (f ⁻¹ᵁ U).ι.continuous).map p.continuous
    exact hspec.mem_closed (hC.union hD) (hcover hpa)

end AlgebraicGeometry

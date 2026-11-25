/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete

/-!
# Isolated points in fibres of unramified morphisms

Source: Stacks Project, Morphisms, Definition 02G4 and Lemma 02G7
(blueprint: lem-weil-pbc-unramified-fibre-point-isolated)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A point unramified in a locally finite type morphism is isolated in its fibre.

Source: Stacks Project, Morphisms, Definition 02G4 and Lemma 02G7.
(blueprint: lem-weil-pbc-unramified-fibre-point-isolated)

Proof:
1. Choose the unramified open neighbourhood `U` of `x`. Its residue-field fibre is
   unramified by `lem-weil-pbc-unramified-base-change-open`, clause (1).
2. Apply `lem-weil-pbc-unramified-over-field-discrete` over the field `S.residueField (f x)`:
   every singleton in this neighbourhood's fibre is open.
3. By `lem-weil-pbc-open-fibre-product`, the fibre of `U` is an open subscheme of
   `f.fiber (f x)`, with image the inverse image of `U` under `f.fiberι (f x)` and
   compatible first projections.
4. The canonical point `f.asFiber x` lies in this open image, so its singleton is open
   in the whole fibre. The homeomorphism `f.fiberHomeo (f x)` from `def-pc-scheme-fibre`
   identifies this singleton with the singleton of `x` in the subspace `f ⁻¹' {f x}`.
   The same homeomorphism gives uniqueness of the point over `x`.
-/
theorem unramified_fibre_point_isolated
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (h_unramified : ∃ U : X.Opens, x ∈ U ∧
      (LocallyOfFiniteType (U.ι ≫ f) ∧
        IsOpenImmersion (pullback.diagonal (U.ι ≫ f)))) :
    IsOpen ({f.asFiber x} : Set (f.fiber (f x))) ∧
      (∀ ξ : f.fiber (f x), f.fiberι (f x) ξ = x → ξ = f.asFiber x) ∧
      IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})) := by
  obtain ⟨U, hxU, hU⟩ := h_unramified
  let g := S.fromSpecResidueField (f x)
  let f' := U.ι ≫ f
  have hbase := unramified_baseChange_restrict_open f' hU g
  have : LocallyOfFiniteType (pullback.snd f' g) := hbase.1
  have : IsOpenImmersion (pullback.diagonal (pullback.snd f' g)) := hbase.2.1
  have : DiscreteTopology (pullback f' g : Scheme.{u}) :=
    discreteTopology_of_unramified_over_field (pullback.snd f' g)
  let j : pullback f' g ⟶ f.fiber (f x) :=
    pullback.map f' g f g U.ι (𝟙 _) (𝟙 S) (by simp [f']) (by simp)
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hxj : f.asFiber x ∈ Set.range j := by
    change f.asFiber x ∈ Set.range
      (pullback.map f' g f g U.ι (𝟙 _) (𝟙 S) (by simp [f']) (by simp))
    rw [Scheme.Pullback.range_map]
    constructor
    · exact ⟨⟨x, hxU⟩, (f.fiberι_asFiber x).symm⟩
    · exact ⟨_, rfl⟩
  obtain ⟨ξ', hξ'⟩ := hxj
  have hopen : IsOpen ({f.asFiber x} : Set (f.fiber (f x))) := by
    simpa [Set.image_singleton, hξ'] using
      j.isOpenEmbedding.isOpenMap {ξ'} (isOpen_discrete _)
  refine ⟨hopen, ?_, ?_⟩
  · intro ξ hξ
    apply (f.fiberι (f x)).isEmbedding.injective
    rw [hξ, f.fiberι_asFiber]
  · rw [← (f.fiberHomeo (f x)).symm.isOpen_image]
    simpa [Scheme.Hom.asFiber] using hopen

end AlgebraicGeometry

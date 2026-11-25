/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Affine morphisms

`AlgebraicGeometry.isAffineHom_tfae`: a morphism `f : X ⟶ Y` is affine if and only if the
preimage of every affine open of `Y` is affine, if and only if there is a cover of `Y` by affine
opens with affine preimages (Stacks Project Tag 01S8).

## Nonempty opens of an affine curve are affine

Let `X` be an irreducible affine scheme whose underlying space is noetherian of dimension at most
one, and `j : U ⟶ X` an open immersion with nonempty source. Then `j` is an affine morphism, so
`U` is affine.

Near a point `x` of the range of `j`, a basic open of `X` inside the range does it. Near a point
`x` outside the range, which is closed, choose a basic open `D(f)` containing the generic point
but not `x`; its complement `V(f)` is finite, as is the complement of the range of `j`, and a
basic open `D(g)` around `x` avoiding the other points of both meets the range of `j` in
`D(g) ∖ {x} = D(fg)`.
-/

@[expose] public section

universe u

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

/-- **Affineness is local on the target** (Stacks Project Tag 01S8): for a morphism of schemes
`f : X ⟶ Y` the following are equivalent:
1. `f` is affine;
2. the preimage of every affine open of `Y` is affine;
3. there is a cover of `Y` by affine opens whose preimages are affine.
(blueprint: `pqf-lem-affine-local-target`; the definition `pqf-def-affine-morphism` is
`AlgebraicGeometry.IsAffineHom`) -/
@[stacks 01S8]
theorem isAffineHom_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE [IsAffineHom f, ∀ U : Y.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U),
      ∃ (ι : Type u) (U : ι → Y.affineOpens), ⨆ i, (U i : Y.Opens) = ⊤ ∧
        ∀ i, IsAffineOpen (f ⁻¹ᵁ (U i : Y.Opens))] := by
  tfae_have 1 → 2 := fun _ U hU ↦ hU.preimage f
  tfae_have 2 → 3 := fun H ↦ ⟨Y.affineOpens, id, by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩, fun U ↦ H U U.2⟩
  tfae_have 3 → 1 := fun ⟨ι, U, hU, H⟩ ↦
    (HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom) U hU).mpr H
  tfae_finish

section Curve

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- A point of an affine scheme has a basic open neighbourhood inside any open neighbourhood. -/
lemma exists_basicOpen_le_of_mem [IsAffine X] {x : X} {W : Set X} (hW : IsOpen W)
    (hx : x ∈ W) : ∃ g : Γ(X, ⊤), x ∈ X.basicOpen g ∧ (X.basicOpen g : Set X) ⊆ W := by
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgW⟩ :=
    (Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen X) (U := ⟨W, hW⟩) hx)
  exact ⟨g, hxg, hgW⟩

/-- An open immersion with nonempty source into an irreducible affine scheme whose underlying
space is noetherian of dimension at most one is an affine morphism. -/
theorem isAffineHom_of_isOpenImmersion_of_topologicalKrullDim_le_one [IsAffine X]
    [IrreducibleSpace X] [NoetherianSpace X] (h : topologicalKrullDim X ≤ 1) [Nonempty U] :
    IsAffineHom j := by
  have hne : (Set.range j.base).Nonempty := Set.range_nonempty _
  have hopen : IsOpen (Set.range j.base) := j.isOpenEmbedding.isOpen_range
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun x ↦ ?_
  -- it suffices to find a basic open `D(g) ∋ x` meeting the range of `j` in a basic open
  suffices H : ∃ g h : Γ(X, ⊤), x ∈ X.basicOpen g ∧ X.basicOpen h ≤ j.opensRange ∧
      X.basicOpen g ⊓ j.opensRange = X.basicOpen h by
    obtain ⟨g, h, hxg, hh, hgh⟩ := H
    refine ⟨X.basicOpen g, hxg, (isAffineOpen_top X).basicOpen g, ?_⟩
    have : j ⁻¹ᵁ X.basicOpen g = j ⁻¹ᵁ X.basicOpen h := by
      rw [← hgh, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_opensRange, inf_top_eq]
    rw [this]
    exact ((isAffineOpen_top X).basicOpen h).preimage_of_isOpenImmersion j hh
  by_cases hx : x ∈ Set.range j.base
  · obtain ⟨g, hxg, hg⟩ := exists_basicOpen_le_of_mem hopen hx
    exact ⟨g, g, hxg, hg, inf_eq_left.mpr hg⟩
  · -- `x` is a closed point outside the range
    have hxc : IsClosed ({x} : Set X) := hopen.isClosed_singleton_of_mem_compl h hne hx
    -- a basic open containing the generic point but not `x`
    have hηr : genericPoint X ∈ Set.range j.base :=
      ((genericPoint_spec X).mem_open_set_iff hopen).mpr (by simpa using hne)
    have hη : genericPoint X ∈ ({x}ᶜ : Set X) := fun hηx ↦ hx (hηx ▸ hηr)
    obtain ⟨f, hηf, hfx⟩ := exists_basicOpen_le_of_mem hxc.isOpen_compl hη
    have hfne : (X.basicOpen f : Set X).Nonempty := ⟨_, hηf⟩
    have hVf : ((X.basicOpen f : Set X)ᶜ).Finite :=
      (X.basicOpen f).isOpen.finite_compl_of_topologicalKrullDim_le_one h hfne
    have hZ : (Set.range j.base)ᶜ.Finite := hopen.finite_compl_of_topologicalKrullDim_le_one h hne
    -- the other points of `V(f)` and of the complement of the range form a closed set
    set S : Set X := ((X.basicOpen f : Set X)ᶜ ∪ (Set.range j.base)ᶜ) \ {x} with hS
    have hSc : IsClosed S := by
      have hfin : S.Finite := (hVf.union hZ).sdiff
      rw [← Set.biUnion_of_singleton S]
      refine hfin.isClosed_biUnion fun s hs ↦ ?_
      rcases hs.1 with hs | hs
      · exact (X.basicOpen f).isOpen.isClosed_singleton_of_mem_compl h hfne hs
      · exact hopen.isClosed_singleton_of_mem_compl h hne hs
    have hxS : x ∈ Sᶜ := fun hxS ↦ hxS.2 rfl
    obtain ⟨g, hxg, hgS⟩ := exists_basicOpen_le_of_mem hSc.isOpen_compl hxS
    -- on `D(g)`, the range of `j` is `D(f)`
    have key (y : X) (hy : y ∈ X.basicOpen g) : y ∈ Set.range j.base ↔ y ∈ X.basicOpen f := by
      by_cases hyx : y = x
      · subst hyx
        exact iff_of_false hx fun hyf ↦ hfx hyf rfl
      · have hyS : y ∉ S := hgS hy
        simp only [hS, Set.mem_sdiff, Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
          not_and, not_not] at hyS
        constructor <;> intro _ <;> by_contra hc <;> exact hyx (hyS (by tauto))
    refine ⟨g, f * g, hxg, fun y hy ↦ ?_, ?_⟩
    · rw [Scheme.basicOpen_mul] at hy
      exact (key y hy.2).mpr hy.1
    · rw [Scheme.basicOpen_mul]
      ext y
      simp only [Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Scheme.Hom.coe_opensRange]
      constructor
      · rintro ⟨hyg, hyr⟩
        exact ⟨(key y hyg).mp hyr, hyg⟩
      · rintro ⟨hyf, hyg⟩
        exact ⟨hyg, (key y hyg).mpr hyf⟩

include j in
/-- A nonempty open subscheme of an irreducible affine scheme whose underlying space is
noetherian of dimension at most one is affine. -/
theorem isAffine_of_isOpenImmersion_of_topologicalKrullDim_le_one [IsAffine X]
    [IrreducibleSpace X] [NoetherianSpace X] (h : topologicalKrullDim X ≤ 1) [Nonempty U] :
    IsAffine U :=
  have := isAffineHom_of_isOpenImmersion_of_topologicalKrullDim_le_one j h
  isAffine_of_isAffineHom j

end Curve

end AlgebraicGeometry

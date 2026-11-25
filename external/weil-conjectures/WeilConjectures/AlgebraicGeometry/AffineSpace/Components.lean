/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection

/-!
# Connected components of relative affine space and of the complement of the zero section

For a scheme `B` and the projection `π : 𝔸(n; B) ⟶ B`, `n` nonempty, the connected components
of `𝔸(n; B)` are the inverse images of the connected components of `B`, and likewise for the
complement `G` of the zero section (`G = 𝔾_{m, B}` for `n` a singleton). In particular every
connected component of `𝔸(n; B)` meets `G`, and every connected component of either meets the
image of the unit section `t = 1` (blueprint `lemma-section-normal-bundle--1`).

The argument is the one of the blueprint: `π` is open and surjective, hence a quotient map, and
its fibres are irreducible, hence connected; the same holds for `π ∘ j` with `j : G ⟶ 𝔸(n; B)`
the open immersion, whose fibres are nonempty open subsets of the irreducible fibres of `π`.
Unlike the blueprint, no noetherian hypothesis on `B` is needed.

## Implementation notes

The complement of the zero section is not a Mathlib scheme, so it is carried as data: a scheme
`G` with an open immersion `j` whose range is the complement of the range of the zero section,
as in `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`.

## Main statements

- `AlgebraicGeometry.AffineSpace.preimage_connectedComponent_over`
- `AlgebraicGeometry.AffineSpace.preimage_connectedComponent_comp_over`
- `AlgebraicGeometry.AffineSpace.exists_mem_connectedComponent_range_oneSection`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineSpace

variable {n : Type u} {B : Scheme.{u}}

/-- The unit section lies in the complement of the zero section. -/
lemma oneSection_mem_range_of_range_eq [Nonempty n] {G : Scheme.{u}} {j : G ⟶ 𝔸(n; B)}
    (hj : Set.range j = (Set.range (zeroSection n B))ᶜ) (y : B) :
    oneSection n B y ∈ Set.range j := by
  rw [hj]
  exact oneSection_apply_notMem_range_zeroSection n B y

/-- The fibres of `𝔸(n; B) ⟶ B` are connected. -/
lemma isConnected_preimage_singleton_over (y : B) :
    _root_.IsConnected ((𝔸(n; B) ↘ B) ⁻¹' {y}) :=
  ((𝔸(n; B) ↘ B).isIrreducible_preimage (isOpenMap_over (n := n) B)
    isIrreducible_singleton).isConnected

/-- The fibres of `G ⟶ B`, for `G` the complement of the zero section, are connected: they are
nonempty open subsets of the irreducible fibres of `𝔸(n; B) ⟶ B`. -/
lemma isConnected_preimage_singleton_comp_over [Nonempty n] {G : Scheme.{u}} (j : G ⟶ 𝔸(n; B))
    [IsOpenImmersion j] (hj : Set.range j = (Set.range (zeroSection n B))ᶜ) (y : B) :
    _root_.IsConnected ((j ≫ 𝔸(n; B) ↘ B) ⁻¹' {y}) := by
  have hF : IsIrreducible ((𝔸(n; B) ↘ B) ⁻¹' {y}) :=
    (𝔸(n; B) ↘ B).isIrreducible_preimage (isOpenMap_over (n := n) B) isIrreducible_singleton
  obtain ⟨g, hg⟩ := oneSection_mem_range_of_range_eq hj y
  have hne : (j ⁻¹' ((𝔸(n; B) ↘ B) ⁻¹' {y})).Nonempty :=
    ⟨g, by simp [hg, ← Scheme.Hom.comp_apply]⟩
  refine ⟨hne, ?_⟩
  exact
    (hF.isPreirreducible.preimage j.isOpenEmbedding).isPreconnected

/-- The projection `𝔸(n; B) ⟶ B` is a quotient map, being open, continuous and surjective. -/
lemma isCoinducing_over : Topology.IsCoinducing (𝔸(n; B) ↘ B) :=
  ((isOpenMap_over (n := n) B).isQuotientMap (𝔸(n; B) ↘ B).continuous
    fun y ↦ ⟨oneSection n B y, by simp [← Scheme.Hom.comp_apply]⟩).isCoinducing

/-- The projection `G ⟶ B` from the complement of the zero section is a quotient map. -/
lemma isCoinducing_comp_over [Nonempty n] {G : Scheme.{u}} (j : G ⟶ 𝔸(n; B)) [IsOpenImmersion j]
    (hj : Set.range j = (Set.range (zeroSection n B))ᶜ) :
    Topology.IsCoinducing (j ≫ 𝔸(n; B) ↘ B) := by
  refine (IsOpenMap.isQuotientMap ?_ (j ≫ 𝔸(n; B) ↘ B).continuous fun y ↦ ?_).isCoinducing
  · change IsOpenMap (fun x ↦ (𝔸(n; B) ↘ B) (j x))
    exact (isOpenMap_over (n := n) B).comp j.isOpenEmbedding.isOpenMap
  · obtain ⟨g, hg⟩ := oneSection_mem_range_of_range_eq hj y
    exact ⟨g, by simp [hg, ← Scheme.Hom.comp_apply]⟩

/-- Blueprint `lemma-section-normal-bundle--1` (1), for the affine space: the connected components
of `𝔸(n; B)` are exactly the inverse images of the connected components of `B`. -/
theorem preimage_connectedComponent_over (x : 𝔸(n; B)) :
    (𝔸(n; B) ↘ B) ⁻¹' connectedComponent ((𝔸(n; B) ↘ B) x) = connectedComponent x :=
  isCoinducing_over.preimage_connectedComponent isConnected_preimage_singleton_over x

/-- Blueprint `lemma-section-normal-bundle--1` (1), for the complement of the zero section: the
connected components of `G = 𝔸(n; B) ∖ 0(B)` are exactly the inverse images of the connected
components of `B`. -/
theorem preimage_connectedComponent_comp_over [Nonempty n] {G : Scheme.{u}} (j : G ⟶ 𝔸(n; B))
    [IsOpenImmersion j] (hj : Set.range j = (Set.range (zeroSection n B))ᶜ) (g : G) :
    (j ≫ 𝔸(n; B) ↘ B) ⁻¹' connectedComponent ((j ≫ 𝔸(n; B) ↘ B) g) = connectedComponent g :=
  (isCoinducing_comp_over j hj).preimage_connectedComponent
    (isConnected_preimage_singleton_comp_over j hj) g

/-- Blueprint `lemma-section-normal-bundle--1` (2), (3): every connected component of a space over
`B` whose components are inverse images of components of `B` meets the image of any section. -/
lemma exists_mem_connectedComponent_range_of_preimage {T : Scheme.{u}} (p : T ⟶ B)
    (s : B ⟶ T) (hs : s ≫ p = 𝟙 B)
    (hp : ∀ x, p ⁻¹' connectedComponent (p x) = connectedComponent x) (x : T) :
    (connectedComponent x ∩ Set.range s).Nonempty :=
  ⟨s (p x), by
    have h : p (s (p x)) = p x := by
      rw [← Scheme.Hom.comp_apply, hs]
      rfl
    rw [← hp, Set.mem_preimage, h]
    exact mem_connectedComponent, p x, rfl⟩

/-- Blueprint `lemma-section-normal-bundle--1`: The connected components of the affine line over a
base.

(2), first half: every connected component of `𝔸(n; B)` meets the image of the unit section. -/
theorem exists_mem_connectedComponent_range_oneSection (x : 𝔸(n; B)) :
    (connectedComponent x ∩ Set.range (oneSection n B)).Nonempty :=
  exists_mem_connectedComponent_range_of_preimage _ _ (oneSection_comp_over n B)
    preimage_connectedComponent_over x

/-- Blueprint `lemma-section-normal-bundle--1`: The connected components of the affine line over a
base.

(2), second half: every connected component of `𝔸(n; B)` meets the complement `G` of the zero
section. -/
theorem exists_mem_connectedComponent_range_of_range_eq [Nonempty n] {G : Scheme.{u}}
    {j : G ⟶ 𝔸(n; B)}
    (hj : Set.range j = (Set.range (zeroSection n B))ᶜ) (x : 𝔸(n; B)) :
    (connectedComponent x ∩ Set.range j).Nonempty := by
  obtain ⟨_, hx, y, rfl⟩ := exists_mem_connectedComponent_range_oneSection x
  exact ⟨_, hx, oneSection_mem_range_of_range_eq hj y⟩

/-- Blueprint `lemma-section-normal-bundle--1`: The connected components of the affine line over a
base.

(3): every connected component of the complement `G` of the zero section meets the image of
the unit section `i₁ : B ⟶ G`. -/
theorem exists_mem_connectedComponent_range_of_comp_eq_oneSection [Nonempty n]
    {G : Scheme.{u}}
    (j : G ⟶ 𝔸(n; B)) [IsOpenImmersion j] (hj : Set.range j = (Set.range (zeroSection n B))ᶜ)
    (i₁ : B ⟶ G) (hi₁ : i₁ ≫ j = oneSection n B) (g : G) :
    (connectedComponent g ∩ Set.range i₁).Nonempty :=
  exists_mem_connectedComponent_range_of_preimage (j ≫ 𝔸(n; B) ↘ B) i₁
    (by rw [reassoc_of% hi₁, oneSection_comp_over]) (preimage_connectedComponent_comp_over j hj) g

end AlgebraicGeometry.AffineSpace

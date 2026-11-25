/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The zero section of affine space as a zero locus

The zero section `0 : S ⟶ 𝔸(n; S)` identifies `S` with the closed subscheme `V(t_i)` of
`𝔸(n; S)` cut out by the coordinates: the coordinates vanish along the zero section, so it
factors through `V(t_i)`, and the composite `V(t_i) ⟶ 𝔸(n; S) ⟶ S` is inverse to the
factorisation since a morphism to `𝔸(n; S)` is determined by its composite with the projection
and the pullbacks of the coordinates.

## Main definitions

- `AlgebraicGeometry.AffineSpace.zeroSectionIsoZeroLocusSubscheme`: `S ≅ V(t_i)`, compatibly
  with the zero section and the inclusion of `V(t_i)`.

## Main statements

- `AlgebraicGeometry.AffineSpace.dense_compl_range_zeroSection`: the complement of the zero
  section is dense, the fibres of `𝔸(n; S) ⟶ S` being irreducible.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineSpace

variable (n : Type u) (S : Scheme.{u})

/-- The zero section identifies `S` with the closed subscheme of `𝔸(n; S)` cut out by the
coordinates. The set `s` of sections is an argument with `Set.range (coord S) = s`, so that the
isomorphism applies to any presentation of that set, for instance `{coord S i}` when `n` has a
single element. -/
noncomputable def zeroSectionIsoZeroLocusSubscheme {s : Set Γ(𝔸(n; S), ⊤)}
    (hs : Set.range (coord S) = s) : S ≅ 𝔸(n; S).zeroLocusSubscheme s where
  hom := (zeroSection n S).liftZeroLocusSubscheme (by
    rintro _ ht
    obtain ⟨i, rfl⟩ := hs ▸ ht
    exact zeroSection_appTop_coord n S i)
  inv := 𝔸(n; S).zeroLocusSubschemeι s ≫ 𝔸(n; S) ↘ S
  hom_inv_id := by simp
  inv_hom_id := by
    rw [← cancel_mono (𝔸(n; S).zeroLocusSubschemeι s)]
    simp only [Category.assoc, Scheme.Hom.liftZeroLocusSubscheme_zeroLocusSubschemeι,
      Category.id_comp]
    refine AffineSpace.hom_ext (by simp) (fun i ↦ ?_)
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zeroSection_appTop_coord,
      map_zero]
    exact (Scheme.zeroLocusSubschemeι_appTop (hs ▸ ⟨i, rfl⟩)).symm

@[reassoc (attr := simp)]
lemma zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι {s : Set Γ(𝔸(n; S), ⊤)}
    (hs : Set.range (coord S) = s) :
    (zeroSectionIsoZeroLocusSubscheme n S hs).hom ≫ 𝔸(n; S).zeroLocusSubschemeι s =
      zeroSection n S := by
  simp [zeroSectionIsoZeroLocusSubscheme]

/-- The unit section of affine space misses the zero section: the coordinates are `1` along the
former and `0` along the latter, so the basic open of a coordinate separates them. -/
lemma oneSection_apply_notMem_range_zeroSection [Nonempty n] (y : S) :
    oneSection n S y ∉ Set.range (zeroSection n S) := by
  rintro ⟨y', hy'⟩
  let i : n := Classical.arbitrary n
  have h₁ : oneSection n S y ∈ 𝔸(n; S).basicOpen (coord S i) := by
    change y ∈ oneSection n S ⁻¹ᵁ 𝔸(n; S).basicOpen (coord S i)
    rw [Scheme.preimage_basicOpen_top, oneSection, homOfVector_appTop_coord]
    simp
  have h₀ : zeroSection n S y' ∉ 𝔸(n; S).basicOpen (coord S i) := by
    change y' ∉ zeroSection n S ⁻¹ᵁ 𝔸(n; S).basicOpen (coord S i)
    rw [Scheme.preimage_basicOpen_top, zeroSection_appTop_coord]
    simp
  exact h₀ (hy' ▸ h₁)

/-- **The complement of the zero section is dense.** The zero section of `𝔸(n; S)`, `n`
nonempty, has empty interior: the fibre of `𝔸(n; S) ⟶ S` through a point `0(y)` is irreducible,
so its generic point specializes both to `0(y)` and to `1(y)`, and an open subset of the closed
zero section containing `0(y)` would contain the generic point and hence `1(y)`. -/
theorem dense_compl_range_zeroSection [Nonempty n] :
    Dense (Set.range (zeroSection n S))ᶜ := by
  rw [← interior_eq_empty_iff_dense_compl, Set.eq_empty_iff_forall_notMem]
  rintro _ hx
  obtain ⟨y, rfl⟩ := interior_subset hx
  have hF : IsIrreducible ((𝔸(n; S) ↘ S) ⁻¹' {y}) :=
    (𝔸(n; S) ↘ S).isIrreducible_preimage (isOpenMap_over (n := n) S) isIrreducible_singleton
  have hg := hF.isGenericPoint_genericPoint_closure
  have h₀ : hF.genericPoint ⤳ zeroSection n S y := hg.specializes (subset_closure (by
    simp [← Scheme.Hom.comp_apply]))
  have h₁ : hF.genericPoint ⤳ oneSection n S y := hg.specializes (subset_closure (by
    simp [← Scheme.Hom.comp_apply]))
  have hmem := h₀.mem_open isOpen_interior hx
  have hclosed : IsClosed (Set.range (zeroSection n S)) :=
    (zeroSection n S).isClosedEmbedding.isClosed_range
  exact oneSection_apply_notMem_range_zeroSection n S y
    (h₁.mem_closed hclosed (interior_subset hmem))

end AlgebraicGeometry.AffineSpace

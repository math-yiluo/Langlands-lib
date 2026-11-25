/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import WeilConjectures.AlgebraicGeometry.GenericFiniteness
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Generic finiteness of quasi-finite morphisms to irreducible schemes

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isFinite_preimage_of_locallyQuasiFinite`: a separated,
  quasi-compact, locally quasi-finite morphism of finite type `e : W ⟶ Y` to an irreducible
  scheme whose image contains the generic point is finite over a nonempty open `O ⊆ Y` with
  nonempty preimage.
- `AlgebraicGeometry.Scheme.Hom.exists_isFinite_preimage_of_etale`: the same for étale
  morphisms from a nonempty scheme, the generic point being automatically in the (open) image.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Generic finiteness of quasi-finite morphisms.** A separated, quasi-compact, locally
quasi-finite morphism of finite type `e : W ⟶ Y` to an irreducible scheme whose image contains
the generic point of `Y` is finite over a nonempty open `O` of `Y` with nonempty preimage. -/
theorem Scheme.Hom.exists_isFinite_preimage_of_locallyQuasiFinite {W Y : Scheme.{u}}
    (e : W ⟶ Y) [LocallyQuasiFinite e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsSeparated e] [IrreducibleSpace Y] (he : genericPoint Y ∈ Set.range e) :
    ∃ O : Y.Opens, (O : Set Y).Nonempty ∧ (e ⁻¹ᵁ O : Set W).Nonempty ∧ IsFinite (e ∣_ O) := by
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hηU₀, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : IrreducibleSpace (Scheme.Opens.toScheme U₀) := Subtype.irreducibleSpace
    ⟨⟨_, hηU₀⟩, (IrreducibleSpace.isIrreducible_univ Y).2.open_subset U₀.isOpen
      (Set.subset_univ _)⟩
  have : IsAffine (Scheme.Opens.toScheme U₀) := hU₀
  obtain ⟨U₁, hη, hfin⟩ := (e ∣_ U₀).exists_isFinite_morphismRestrict_of_irreducibleSpace
  have hO : (Scheme.Opens.ι U₀ ''ᵁ U₁ : Set Y).Nonempty := ⟨_, _, hη, rfl⟩
  obtain ⟨w, hw⟩ := he
  refine ⟨Scheme.Opens.ι U₀ ''ᵁ U₁, hO, ⟨w, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, hw]
    exact ((genericPoint_spec Y).mem_open_set_iff (Scheme.Opens.ι U₀ ''ᵁ U₁).isOpen).2
      (by simpa using hO)
  · exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict e U₀ U₁)).1 hfin

/-- **Generic finiteness of étale morphisms.** A separated quasi-compact étale morphism
`e : W ⟶ Y` from a nonempty scheme to an irreducible scheme is finite over a nonempty open `O`
of `Y` with nonempty preimage. -/
theorem Scheme.Hom.exists_isFinite_preimage_of_etale {W Y : Scheme.{u}} (e : W ⟶ Y) [Etale e]
    [QuasiCompact e] [IsSeparated e] [IrreducibleSpace Y] [Nonempty W] :
    ∃ O : Y.Opens, (O : Set Y).Nonempty ∧ (e ⁻¹ᵁ O : Set W).Nonempty ∧ IsFinite (e ∣_ O) :=
  e.exists_isFinite_preimage_of_locallyQuasiFinite <|
    ((genericPoint_spec Y).mem_open_set_iff e.isOpenMap.isOpen_range).2
      (by simpa using Set.range_nonempty e)

end AlgebraicGeometry

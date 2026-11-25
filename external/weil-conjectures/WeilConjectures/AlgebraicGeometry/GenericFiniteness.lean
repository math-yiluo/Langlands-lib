/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Generic finiteness of quasi-finite morphisms

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_irreducibleSpace`: a
  separated quasi-compact locally quasi-finite morphism of finite type to an irreducible affine
  scheme is finite over a neighbourhood of the generic point (Stacks 02NW).
- `AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_noetherianSpace`: a locally
  quasi-finite morphism of finite type from an affine scheme to a scheme with Noetherian
  underlying space is finite over a nonempty open.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Inside a fibre of a locally quasi-finite morphism there are no nontrivial specializations: the
fibres are discrete. -/
lemma Scheme.Hom.eq_of_specializes_of_eq {T S : Scheme.{u}} (p : T ⟶ S) [LocallyQuasiFinite p]
    {a b : T} (h : a ⤳ b) (hab : p a = p b) : a = b := by
  have hd := p.isDiscrete_preimage_singleton (p b)
  have : DiscreteTopology (p ⁻¹' {p b}) := hd.to_subtype
  have h' : (⟨a, hab⟩ : p ⁻¹' {p b}) ⤳ ⟨b, rfl⟩ := by
    exact (Topology.IsInducing.subtypeVal.specializes_iff (x := (⟨a, hab⟩ : p ⁻¹' {p b}))
      (y := ⟨b, rfl⟩)).1 h
  exact congrArg Subtype.val h'.eq

/-- **Generic finiteness of quasi-finite morphisms.** A separated, quasi-compact, locally
quasi-finite morphism of finite type `f : W ⟶ S` to an irreducible affine scheme is finite over
some open neighbourhood of the generic point of `S`.

By Zariski's Main Theorem `W` is a quasi-compact open of a scheme `T` finite over `S`. A point
of the closure of `W` over the generic point `η` is a specialization of a point of `W`, which
also lies over `η`, hence equals it, the fibres of `T` being discrete. So the closed set
`p(closure W \ W)` does not contain `η`, and over its complement `W` is closed in `T`. -/
theorem Scheme.Hom.exists_isFinite_morphismRestrict_of_irreducibleSpace {W S : Scheme.{u}}
    (f : W ⟶ S) [IsAffine S] [IrreducibleSpace S] [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [IsSeparated f] [QuasiCompact f] :
    ∃ U : S.Opens, genericPoint S ∈ U ∧ IsFinite (f ∣_ U) := by
  obtain ⟨T, j, p, hj, hjc, hp, hjp⟩ := f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  have : IsAffine T := isAffine_of_isAffineHom p
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f
  subst hjp
  set η := genericPoint S
  let D : Set T := closure (Set.range j) ∩ (Set.range j)ᶜ
  have hD : IsClosed D := isClosed_closure.inter j.isOpenEmbedding.isOpen_range.isClosed_compl
  have hpD : IsClosed (p '' D) := p.isClosedMap D hD
  have hη : η ∉ p '' D := by
    rintro ⟨t, ⟨ht₁, ht₂⟩, hpt⟩
    obtain ⟨x, hx⟩ := exists_specializes_of_mem_closure_range_of_isAffine j ht₁
    have hpx : p (j x) = η := by
      have h₁ := hx.map p.continuous
      rw [hpt] at h₁
      exact (h₁.antisymm ((genericPoint_spec S).specializes (Set.mem_univ _))).eq
    exact ht₂ ⟨x, p.eq_of_specializes_of_eq hx (hpx.trans hpt.symm)⟩
  let U : S.Opens := ⟨(p '' D)ᶜ, hpD.isOpen_compl⟩
  refine ⟨U, hη, ?_⟩
  rw [morphismRestrict_comp]
  have : IsClosedImmersion (j ∣_ (p ⁻¹ᵁ U)) := by
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    have hr : Set.range (j ∣_ (p ⁻¹ᵁ U)) = (p ⁻¹ᵁ U).ι ⁻¹' closure (Set.range j) := by
      have hι (x) : (p ⁻¹ᵁ U).ι ((j ∣_ (p ⁻¹ᵁ U)) x) = j ((j ⁻¹ᵁ (p ⁻¹ᵁ U)).ι x) := by
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        exact subset_closure ⟨_, (hι x).symm⟩
      · intro hv
        have hvD : v.1 ∉ D := fun h ↦ v.2 ⟨v.1, h, rfl⟩
        obtain ⟨w, hw⟩ : v.1 ∈ Set.range j := by
          by_contra h
          exact hvD ⟨hv, h⟩
        let x : (j ⁻¹ᵁ (p ⁻¹ᵁ U)).toScheme := ⟨w, by
          change j w ∈ p ⁻¹ᵁ U
          rw [hw]
          exact v.2⟩
        exact ⟨x, Subtype.ext ((hι x).trans hw)⟩
    rw [hr]
    exact isClosed_closure.preimage (p ⁻¹ᵁ U).ι.continuous
  infer_instance

/-- **Generic finiteness of quasi-finite morphisms.** A locally quasi-finite morphism of finite
type `f : X ⟶ Z` from an affine scheme to a nonempty scheme with Noetherian underlying space is
finite over some nonempty open of `Z`: apply
`AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_of_irreducibleSpace` over an
irreducible affine open of `Z`. -/
theorem Scheme.Hom.exists_isFinite_morphismRestrict_of_noetherianSpace {X Z : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Z] [Nonempty Z] (f : X ⟶ Z) [IsAffine X]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ IsFinite (f ∣_ U) := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  obtain ⟨C, hC, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {z}
    isIrreducible_singleton
  obtain ⟨o, ho, ⟨z', hz'⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hzU₀, hU₀o⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open hz' ho
  have hirr : IsIrreducible (U₀ : Set Z) :=
    ⟨⟨z', hzU₀⟩, hC.1.2.open_subset U₀.isOpen (hU₀o.trans hoC)⟩
  have : IrreducibleSpace (Scheme.Opens.toScheme U₀) := Subtype.irreducibleSpace hirr
  have : IsAffine (Scheme.Opens.toScheme U₀) := hU₀
  have : QuasiCompact f := by
    have : QuasiCompact (f ≫ terminal.from Z) := by rw [terminal.comp_from]; infer_instance
    exact QuasiCompact.of_comp f (terminal.from Z)
  have : IsSeparated (f ∣_ U₀) := by
    have : IsSeparated ((f ∣_ U₀) ≫ terminal.from (Scheme.Opens.toScheme U₀)) := by
      rw [terminal.comp_from, ← terminal.comp_from (f ⁻¹ᵁ U₀).ι]
      infer_instance
    exact IsSeparated.of_comp _ (terminal.from (Scheme.Opens.toScheme U₀))
  obtain ⟨U₁, hη, hfin⟩ := (f ∣_ U₀).exists_isFinite_morphismRestrict_of_irreducibleSpace
  refine ⟨Scheme.Opens.ι U₀ ''ᵁ U₁, ⟨_, ⟨_, hη, rfl⟩⟩, ?_⟩
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict f U₀ U₁)).1 hfin

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.RingTheory.ProperBaseChange.MinimalPrimeFiniteTypeFiniteAway
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Finiteness over an open containing all component generic points

## References

* Stacks Project, Morphisms of Schemes, Tag 02NW, equivalence (1) and (4), applied to every
  component generic point
* Stacks Project, Tag 02NW, (1) implies (4), followed by union over component generic points
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

private theorem generic_fiber_subset_genericPoints
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    {η : Y} (hη : η ∈ genericPoints Y) (hf : (f ⁻¹' {η}).Finite) :
    f ⁻¹' {η} ⊆ genericPoints X := by
  have hd := (f.discreteTopology_fiber_and_quasiFiniteAt η hf).2.1
  have : DiscreteTopology (f ⁻¹' {η}) := (f.fiberHomeo η).discreteTopology
  intro x hx
  apply mem_genericPoints_iff_forall_specializes.mpr
  intro z hz
  have hzη : f z = η :=
    mem_genericPoints_iff_forall_specializes.mp hη (f z)
      (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
        (hx ▸ hz.map f.continuous))
  have hsub : (⟨z, hzη⟩ : f ⁻¹' {η}) ⤳ ⟨x, hx⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp hz
  exact congrArg Subtype.val hsub.eq

private theorem affine_generic_finite_neighborhood
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.FiniteType)
    (p : PrimeSpectrum R) (hp : p ∈ genericPoints (PrimeSpectrum R))
    (hf : ((Spec.map φ) ⁻¹' {p}).Finite) :
    ∃ V : (Spec R).Opens, p ∈ V ∧ IsFinite (Spec.map φ ∣_ V) := by
  have hp' : p.asIdeal ∈ minimalPrimes R := PrimeSpectrum.mem_genericPoints_iff.mp hp
  have hf' : {q : PrimeSpectrum S | Ideal.comap φ.hom q.asIdeal = p.asIdeal}.Finite := by
    apply hf.subset
    intro q hq
    exact PrimeSpectrum.ext hq
  obtain ⟨g, hg, hfin⟩ :=
    RingHom.exists_finite_awayMap_of_finite_fiber_minimalPrime φ.hom hφ p.asIdeal hp' hf'
  refine ⟨PrimeSpectrum.basicOpen g, hg, ?_⟩
  apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (SpecMapRestrictBasicOpenIso φ g)).mpr
  exact (IsFinite.SpecMap_iff _).mpr hfin

private theorem affine_source_generic_finite_neighborhood
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y] [LocallyOfFiniteType f]
    {η : Y} (hη : η ∈ genericPoints Y) (hf : (f ⁻¹' {η}).Finite) :
    ∃ V : Y.Opens, η ∈ V ∧ IsFinite (f ∣_ V) := by
  let p := Y.isoSpec.hom η
  have hp : p ∈ genericPoints (Spec Γ(Y, ⊤)) := by
    apply mem_genericPoints_iff_forall_specializes.mpr
    intro q hq
    have he := mem_genericPoints_iff_forall_specializes.mp hη
      (Y.isoSpec.inv q) (by
        simpa [p, ← Scheme.Hom.comp_apply] using (hq.map Y.isoSpec.inv.continuous))
    have := congrArg Y.isoSpec.hom he
    simpa [p, ← Scheme.Hom.comp_apply] using this
  have hmap : Spec.map f.appTop = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality f]
    simp
  have hf' : ((Spec.map f.appTop) ⁻¹' {p}).Finite := by
    apply (hf.preimage X.isoSpec.inv.isOpenEmbedding.injective.injOn).subset
    intro q hq
    change f (X.isoSpec.inv q) = η
    apply Y.isoSpec.hom.isOpenEmbedding.injective
    simpa [hmap, Scheme.Hom.comp_apply, p] using hq
  obtain ⟨W, hW, hfin⟩ := affine_generic_finite_neighborhood f.appTop
    ((HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance) p hp hf'
  refine ⟨Y.isoSpec.hom ⁻¹ᵁ W, hW, ?_⟩
  rw [hmap, morphismRestrict_comp] at hfin
  have hfin' : IsFinite ((f ≫ Y.isoSpec.hom) ∣_ W) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) _ _).mp hfin
  rw [morphismRestrict_comp] at hfin'
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite) _ _).mp hfin'

private theorem finite_restrict_of_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) {V W : Y.Opens}
    (hVW : V ≤ W) (hfin : IsFinite (f ∣_ W)) : IsFinite (f ∣_ V) := by
  have hf := IsZariskiLocalAtTarget.restrict (P := @IsFinite) hfin (W.ι ⁻¹ᵁ V)
  have ht := (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f W (W.ι ⁻¹ᵁ V))).mp hf
  have he : W.ι ''ᵁ W.ι ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVW]
  rwa [he] at ht

private theorem remove_complement
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {η : Y} (hη : η ∈ genericPoints Y) (U : X.Opens)
    (hU : f ⁻¹' {η} ⊆ (U : Set X)) :
    ∃ W : Y.Opens, η ∈ W ∧ f ⁻¹ᵁ W ≤ U := by
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)
  let i := I.subschemeι
  let j := i ≫ f
  have hrange : Set.range i = (U : Set X)ᶜ := by
    simp [i, I, Scheme.IdealSheafData.range_subschemeι]
  let W : Y.Opens := ⟨(closure (Set.range j))ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨W, ?_, ?_⟩
  · intro hcl
    obtain ⟨t, ht⟩ := exists_specializes_of_mem_closure_range j hcl
    have htη : j t = η := mem_genericPoints_iff_forall_specializes.mp hη _ ht
    have hnot : i t ∉ U := by
      change i t ∈ (U : Set X)ᶜ
      rw [← hrange]
      exact Set.mem_range_self t
    exact hnot (hU (by simpa [j, Scheme.Hom.comp_apply] using htη))
  · intro x hx
    by_contra hxU
    obtain ⟨t, ht⟩ : x ∈ Set.range i := by rwa [hrange]
    apply hx
    apply subset_closure
    exact ⟨t, by simp [j, ht]⟩

private theorem finite_of_finite_source_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (hle : f ⁻¹ᵁ V ≤ U) (hfin : IsFinite ((U.ι ≫ f) ∣_ V)) :
    IsFinite (f ∣_ V) := by
  let i := U.ι ∣_ (f ⁻¹ᵁ V)
  have hi : Surjective i := ⟨fun x ↦ by
    refine ⟨⟨⟨x.1, hle x.2⟩, x.2⟩, ?_⟩
    apply Subtype.ext
    exact morphismRestrict_base_coe U.ι (f ⁻¹ᵁ V) _⟩
  have : IsIso i := (isIso_iff_isOpenImmersion_and_surjective i).mpr ⟨inferInstance, hi⟩
  rw [morphismRestrict_comp] at hfin
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) i _).mp hfin

private theorem generic_finite_neighborhood_affine_target
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {η : Y} (hη : η ∈ genericPoints Y) (hf : (f ⁻¹' {η}).Finite) :
    ∃ V : Y.Opens, η ∈ V ∧ IsFinite (f ∣_ V) := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨U, hU, hsub⟩ := exists_isAffineOpen_of_subset_genericPoints hf
    (generic_fiber_subset_genericPoints f hη hf)
  have : IsAffine U.toScheme := hU
  have hfU : ((U.ι ≫ f) ⁻¹' {η}).Finite := by
    apply (hf.preimage U.ι.isOpenEmbedding.injective.injOn).subset
    intro x hx
    exact hx
  obtain ⟨V, hηV, hfin⟩ := affine_source_generic_finite_neighborhood (U.ι ≫ f) hη hfU
  obtain ⟨W, hηW, hle⟩ := remove_complement f hη U hsub
  refine ⟨V ⊓ W, ⟨hηV, hηW⟩, ?_⟩
  exact finite_of_finite_source_restrict f U (V ⊓ W)
    (((Opens.map f.base).monotone inf_le_right).trans hle)
    (finite_restrict_of_le (U.ι ≫ f) inf_le_left hfin)

private theorem generic_finite_neighborhood
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    {η : Y} (hη : η ∈ genericPoints Y) (hf : (f ⁻¹' {η}).Finite) :
    ∃ V : Y.Opens, η ∈ V ∧ IsFinite (f ∣_ V) := by
  obtain ⟨V₀, hV₀, hηV₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := η) trivial
  have : IsAffine V₀.toScheme := hV₀
  let η₀ : V₀.toScheme := ⟨η, hηV₀⟩
  have hη₀ : η₀ ∈ genericPoints V₀.toScheme := by
    apply mem_genericPoints_iff_forall_specializes.mpr
    intro y hy
    apply Subtype.ext
    exact mem_genericPoints_iff_forall_specializes.mp hη y.1
      (hy.map V₀.ι.continuous)
  have hf₀ : ((f ∣_ V₀) ⁻¹' {η₀}).Finite := by
    apply (hf.preimage (f ⁻¹ᵁ V₀).ι.isOpenEmbedding.injective.injOn).subset
    intro x hx
    change f x.1 = η
    have he := congrArg Subtype.val hx
    exact (morphismRestrict_base_coe f V₀ x).symm.trans he
  obtain ⟨W, hW, hfin⟩ := generic_finite_neighborhood_affine_target (f ∣_ V₀) hη₀ hf₀
  refine ⟨V₀.ι ''ᵁ W, ⟨η₀, hW, rfl⟩, ?_⟩
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
    (morphismRestrictRestrict f V₀ W)).mp hfin

/-- A quasi-compact, quasi-separated, locally finite type morphism to a Noetherian scheme
with finite set-theoretic fibres at component generic points is finite over a dense open
containing all component generic points.
-/
theorem Scheme.Hom.exists_dense_open_isFinite_of_finite_generic_fibers
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] [CompactSpace Y]
    (hfinite : ∀ (Z : Set Y), Z ∈ irreducibleComponents Y →
      ∀ (η : Y), IsGenericPoint η Z → (f ⁻¹' {η}).Finite) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧
      (∀ (Z : Set Y), Z ∈ irreducibleComponents Y →
        ∀ (η : Y), IsGenericPoint η Z → η ∈ V) ∧
      IsFinite (f ∣_ V) := by
  classical
  let S : Set Y.Opens := {U | IsFinite (f ∣_ U)}
  let U : S → Y.Opens := Subtype.val
  let V : Y.Opens := ⨆ i, U i
  have hgen : genericPoints Y ⊆ (V : Set Y) := by
    intro η hη
    obtain ⟨W, hW, hfin⟩ := generic_finite_neighborhood f hη
      (hfinite (closure {η}) hη η isGenericPoint_closure)
    exact (le_iSup U (⟨W, hfin⟩ : S)) hW
  refine ⟨V, dense_of_genericPoints_subset hgen, ?_, ?_⟩
  · intro Z hZ η hη
    apply hgen
    change closure {η} ∈ irreducibleComponents Y
    rwa [hη.def]
  · apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
      (fun i : S ↦ V.ι ⁻¹ᵁ U i)
    · apply V.ι.image_injective
      change V.ι ''ᵁ (⨆ i : S, V.ι ⁻¹ᵁ U i) = V.ι ''ᵁ ⊤
      rw [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange,
        Scheme.Opens.opensRange_ι]
      simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact iSup_congr fun i ↦ inf_eq_right.mpr (le_iSup U i)
    · intro i
      have he : V.ι ''ᵁ V.ι ⁻¹ᵁ U i = U i := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
          inf_eq_right.mpr (le_iSup U i)]
      apply (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
        (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U i))).mpr
      rw [he]
      exact i.2

end AlgebraicGeometry

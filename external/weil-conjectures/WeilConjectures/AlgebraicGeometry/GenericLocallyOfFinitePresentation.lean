/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Properties

import all WeilConjectures.RingTheory.GenericFlatness
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Generic local finite presentation

Source: Stacks Project, Tags 051T and 052A. The torsion-cover and affine-cover
constructions follow the proved helpers of `WeilConjectures.RingTheory.GenericFlatness` and
`WeilConjectures.AlgebraicGeometry.GenericFlatness`; here the localized isomorphism also
transports finite presentation.
-/

@[expose] public section

universe u
open CategoryTheory
namespace RingHom

private theorem exists_nonzero_finitePresentation_localizationAway {R B : Type u}
    [CommRing R] [CommRing B] [IsDomain R] (φ : R →+* B) (hφ : φ.FiniteType) :
    ∃ a : R, a ≠ 0 ∧ ∀ (T : Type u) [CommRing T] [Algebra B T]
      [IsLocalization.Away (φ a) T], ((algebraMap B T).comp φ).FinitePresentation := by
  let : Algebra R B := φ.toAlgebra
  have : Algebra.FiniteType R B := hφ
  obtain ⟨A, _, _, hfp, f, hf, htors⟩ := exists_finitePresentation_torsion_cover R B
  have : Algebra.FinitePresentation R A := hfp
  obtain ⟨a, ha, hflat⟩ := exists_nonzero_flat_localizationAway (algebraMap R A)
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  refine ⟨a, ha, ?_⟩
  intro T _ _ _
  let C := Localization.Away (algebraMap R A a)
  have : Module.Flat R C := by
    apply RingHom.flat_algebraMap_iff.mp
    exact hflat C
  let : Algebra R T := ((algebraMap B T).comp φ).toAlgebra
  have : IsScalarTower R B T := .of_algebraMap_eq' rfl
  have hfa : f (algebraMap R A a) = φ a := f.commutes a
  have : IsLocalization.Away (f (algebraMap R A a)) T := by rw [hfa]; infer_instance
  let q : C →+* T := IsLocalization.Away.map C T f.toRingHom (algebraMap R A a)
  have hinj : Function.Injective q := by
    apply (IsLocalization.Away.map_injective_iff T f.toRingHom (algebraMap R A a)).mpr
    intro x hx
    obtain ⟨r, hr, hrx⟩ := htors x hx
    have hz : algebraMap A C x = 0 := by
      apply (smul_eq_zero_iff_right hr).mp
      change r • (IsScalarTower.toAlgHom R A C) x = 0
      rw [← map_smul, hrx, map_zero]
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A a)) C x).mp hz
    obtain ⟨n, hn⟩ := m.property
    exact ⟨n, by simpa only [← hn] using hm⟩
  have hsurj : Function.Surjective q := by
    apply (IsLocalization.Away.map_surjective_iff C T f.toRingHom
      (algebraMap R A a)).mpr
    intro b
    obtain ⟨x, rfl⟩ := hf b
    exact ⟨x, 0, by simp⟩
  have hcomm : q.comp ((algebraMap A C).comp (algebraMap R A)) =
      (algebraMap B T).comp φ := by
    ext r
    change q (algebraMap A C (algebraMap R A r)) = algebraMap B T (φ r)
    dsimp only [q, IsLocalization.Away.map]
    rw [IsLocalization.map_eq]
    exact congrArg (algebraMap B T) (f.commutes r)
  rw [← hcomm]
  apply RingHom.FinitePresentation.comp
  · exact RingHom.FinitePresentation.of_bijective ⟨hinj, hsurj⟩
  · change (algebraMap R C).FinitePresentation
    exact RingHom.finitePresentation_algebraMap.mpr inferInstance

end RingHom

namespace AlgebraicGeometry

private theorem exists_nonzero_finitePresentation_restrict_basicOpen {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ a : Γ(S, ⊤), a ≠ 0 ∧ LocallyOfFinitePresentation (f ∣_ S.basicOpen a) := by
  obtain ⟨a, ha, hflat⟩ := RingHom.exists_nonzero_finitePresentation_localizationAway f.appTop.hom
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance)
  refine ⟨a, ha, ?_⟩
  let V : X.Opens := X.basicOpen (f.appTop a)
  have : IsAffine V.toScheme := (isAffineOpen_top X).basicOpen _
  have h : LocallyOfFinitePresentation (V.ι ≫ f) := by
    apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)).mpr
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    convert hflat Γ(V, ⊤) using 1
  apply MorphismProperty.of_postcomp @LocallyOfFinitePresentation (W' := @IsOpenImmersion)
    (f ∣_ S.basicOpen a) (S.basicOpen a).ι inferInstance
  rw [morphismRestrict_ι]
  have heq : f ⁻¹ᵁ S.basicOpen a = V := by
    simpa only [Scheme.Hom.appTop, Scheme.Hom.preimage_top] using Scheme.preimage_basicOpen f a
  rw [heq]
  exact h

private theorem finitePresentation_restrict_of_le {X S : Scheme.{u}} (f : X ⟶ S)
    {U V : S.Opens} (hVU : V ≤ U) [LocallyOfFinitePresentation (f ∣_ U)] :
    LocallyOfFinitePresentation (f ∣_ V) := by
  have h : LocallyOfFinitePresentation (f ∣_ U ∣_ U.ι ⁻¹ᵁ V) := inferInstance
  have h' := (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h
  have heq : U.ι ''ᵁ U.ι ⁻¹ᵁ V = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hVU hx⟩, hx, rfl⟩
  rwa [heq] at h'

private theorem exists_nonempty_open_finitePresentation_restrict_affine_base {X S : Scheme.{u}}
    [IsAffine S] [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ LocallyOfFinitePresentation (f ∣_ U) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have ha (i : 𝒰.I₀) :
      ∃ a : Γ(S, ⊤), a ≠ 0 ∧ LocallyOfFinitePresentation ((𝒰.f i ≫ f) ∣_ S.basicOpen a) := by
    have : IsAffine (𝒰.X i) := by
      dsimp [𝒰, Scheme.OpenCover.finiteSubcover]
      infer_instance
    exact exists_nonzero_finitePresentation_restrict_basicOpen (𝒰.f i ≫ f)
  choose a ha0 haLocallyOfFinitePresentation using ha
  let U : S.Opens := ⨅ i, S.basicOpen (a i)
  have hmem (i : 𝒰.I₀) : genericPoint S ∈ S.basicOpen (a i) := by
    apply ((genericPoint_spec S).mem_open_set_iff (S.basicOpen (a i)).isOpen).mpr
    rw [Set.univ_inter]
    by_contra hn
    apply ha0 i
    exact (basicOpen_eq_bot_iff (a i)).mp ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hn)
  have hU : (U : Set S).Nonempty := by
    refine ⟨genericPoint S, ?_⟩
    dsimp only [U]
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hmem
  refine ⟨U, hU, ?_⟩
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    (𝒰.pullback₁ (f ⁻¹ᵁ U).ι)
  intro i
  have : LocallyOfFinitePresentation ((𝒰.f i ≫ f) ∣_ U) :=
    finitePresentation_restrict_of_le (𝒰.f i ≫ f) (iInf_le (fun i ↦ S.basicOpen (a i)) i)
  rw [morphismRestrict_comp] at this
  let e := CategoryTheory.Limits.pullbackSymmetry (f ⁻¹ᵁ U).ι (𝒰.f i) ≪≫
    pullbackRestrictIsoRestrict (𝒰.f i) (f ⁻¹ᵁ U)
  have heq : (𝒰.pullback₁ (f ⁻¹ᵁ U).ι).f i ≫ f ∣_ U =
      e.hom ≫ (𝒰.f i ∣_ f ⁻¹ᵁ U) ≫ f ∣_ U := by
    change CategoryTheory.Limits.pullback.fst (f ⁻¹ᵁ U).ι (𝒰.f i) ≫ f ∣_ U = _
    simp [e]
  rw [heq]
  infer_instance


/-- A finite type quasi-compact morphism over an integral scheme is locally of finite
presentation after restriction to a nonempty open.

Source: Stacks Project, Tag 052A, finite-presentation part of the generic-flatness
argument. Proof: choose a nonempty affine open Spec A of the base and finitely
many affine charts Spec B_i covering its inverse image. Present each B_i as
A[t]/I. The relation ideal over Frac(A) is finitely generated; clearing denominators
lifts its generators to I. Quotienting by these finitely many lifted relations
gives a finitely presented algebra C_i surjecting onto B_i with A-torsion kernel.
Generic flatness of C_i gives a nonzero a_i for which (C_i)_{a_i} is flat, hence
torsion free, over A_{a_i}. Thus its torsion kernel vanishes and it equals
(B_i)_{a_i}, which is therefore finitely presented over A_{a_i}. Intersect these
finitely many nonempty basic opens. They all contain the generic point, and local
finite presentation on the resulting chart cover implies it for the restricted
map. If the inverse image is empty, the empty intersection is the whole base
chart and source locality is vacuous. Transport the open back into S.
(blueprint: lem-sbc-generic-flat-finite-presentation-lfp) -/
theorem exists_nonempty_open_locallyOfFinitePresentation_restrict {X S : Scheme.{u}}
    [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧
      LocallyOfFinitePresentation (f ∣_ U) := by
  classical
  let x : S := Classical.choice inferInstance
  let V : S.Opens := (S.affineCover.f (S.affineCover.idx x)).opensRange
  have hV : IsAffineOpen V := isAffineOpen_opensRange _
  have hxV : x ∈ V := S.affineCover.covers x
  have : IsAffine V.toScheme := hV
  have : Nonempty V.toScheme := ⟨⟨x, hxV⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  obtain ⟨W, hW, hflat⟩ := exists_nonempty_open_finitePresentation_restrict_affine_base (f ∣_ V)
  refine ⟨V.ι ''ᵁ W, ?_, ?_⟩
  · exact hW.image V.ι
  · exact (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation
      (morphismRestrictRestrict f V W)).mp hflat


end AlgebraicGeometry

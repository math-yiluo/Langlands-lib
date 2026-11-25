/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.RingTheory.Depth

import WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart
import WeilConjectures.AlgebraicGeometry.PolynomialChartFibreFlatCriterion
import WeilConjectures.RingTheory.OpenFlatLocus

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

private theorem maximal_smul_top_ne_top (A : Type*) [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A • (⊤ : Submodule A A)) ≠ ⊤ := by
  rw [Ideal.smul_top_eq_map]
  change (IsLocalRing.maximalIdeal A).map (algebraMap A A) ≠ ⊤
  simpa only [Algebra.algebraMap_self, Ideal.map_id] using
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top

private theorem depth_le_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A ≤ IsLocalRing.depth (R := B) B := by
  classical
  simp only [IsLocalRing.depth, Ideal.depth, maximal_smul_top_ne_top, ↓reduceIte]
  apply sSup_le
  rintro n ⟨rs, hreg, hmem, rfl⟩
  apply le_sSup
  refine ⟨rs.map e, ?_, ?_, by simp⟩
  · apply (e.toAddEquiv.isRegular_congr ?_).mp hreg
    exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
      (fun r _ x ↦ e.map_mul r x))
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e (hmem a ha)

private theorem depth_eq_of_ringEquiv {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    IsLocalRing.depth (R := A) A = IsLocalRing.depth (R := B) B :=
  le_antisymm (depth_le_of_ringEquiv e) (depth_le_of_ringEquiv e.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_locus_source_iff
    {U X T : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : X ⟶ T) (x : U) :
    ((IsLocalRing.depth (R := ((i ≫ f).fiber ((i ≫ f) x)).presheaf.stalk
        ((i ≫ f).asFiber x))
      (((i ≫ f).fiber ((i ≫ f) x)).presheaf.stalk ((i ≫ f).asFiber x)) : WithBot ℕ∞) =
        ringKrullDim (((i ≫ f).fiber ((i ≫ f) x)).presheaf.stalk ((i ≫ f).asFiber x))) ↔
    ((IsLocalRing.depth (R := (f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x)))
      ((f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x))) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x)))) := by
  let q : (i ≫ f).fiber ((i ≫ f) x) ⟶ f.fiber (f (i x)) :=
    Limits.pullback.map (i ≫ f) (T.fromSpecResidueField (f (i x))) f
    (T.fromSpecResidueField (f (i x))) i (𝟙 _) (𝟙 _) (by simp) (by simp)
  have : IsOpenImmersion q :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl (by simp)
  have hpoint : q ((i ≫ f).asFiber x) = f.asFiber (i x) := by
    apply (f.fiberι _).isEmbedding.injective
    have hfst : q ≫ f.fiberι _ = (i ≫ f).fiberι _ ≫ i := by
      simp [q, Scheme.Hom.fiberι]
    have hh := congrArg
      (fun g : (i ≫ f).fiber ((i ≫ f) x) ⟶ X ↦ g ((i ≫ f).asFiber x)) hfst
    simpa only [Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber] using hh
  let e := ((f.fiber (f (i x))).presheaf.stalkCongr (.of_eq hpoint.symm) ≪≫
    asIso (q.stalkMap ((i ≫ f).asFiber x))).commRingCatIsoToRingEquiv
  rw [← ringKrullDim_eq_of_ringEquiv e, ← depth_eq_of_ringEquiv e]

private theorem fibre_depth_eq_ringKrullDim_restrict_iff
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens) (x : (f ⁻¹ᵁ U).toScheme) :
    ((IsLocalRing.depth
        (R := ((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk ((f ∣_ U).asFiber x))
        (((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk ((f ∣_ U).asFiber x)) :
          WithBot ℕ∞) =
      ringKrullDim (((f ∣_ U).fiber ((f ∣_ U) x)).presheaf.stalk
        ((f ∣_ U).asFiber x))) ↔
    ((IsLocalRing.depth (R := (f.fiber (f x.1)).presheaf.stalk (f.asFiber x.1))
        ((f.fiber (f x.1)).presheaf.stalk (f.asFiber x.1)) : WithBot ℕ∞) =
      ringKrullDim ((f.fiber (f x.1)).presheaf.stalk (f.asFiber x.1))) := by
  let tU : U.toScheme := (f ∣_ U) x
  let q := Limits.pullback.map (f ∣_ U) (U.toScheme.fromSpecResidueField tU) f
    (T.fromSpecResidueField (U.ι tU)) (f ⁻¹ᵁ U).ι
    (Spec.map (U.ι.residueFieldMap tU)) U.ι (by simp)
    (by exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField U.ι tU).symm)
  have hsq := isPullback_fiberToSpecResidueField_of_isPullback
    (isPullback_morphismRestrict f U).flip tU
  have : IsIso q := hsq.isIso_fst_of_isIso
  have hbase : U.ι tU = f x.1 := morphismRestrict_base_coe f U x
  let q' : (f ∣_ U).fiber ((f ∣_ U) x) ⟶ f.fiber (f x.1) :=
    q ≫ eqToHom (congrArg f.fiber hbase)
  have : IsIso q' := inferInstance
  have hpoint : q' ((f ∣_ U).asFiber x) = f.asFiber x.1 := by
    apply (f.fiberι _).isEmbedding.injective
    have hfst : q' ≫ f.fiberι (f x.1) =
        (f ∣_ U).fiberι ((f ∣_ U) x) ≫ (f ⁻¹ᵁ U).ι := by
      dsimp [q']
      have heq (t t' : T) (h : t = t') :
          eqToHom (congrArg f.fiber h) ≫ f.fiberι t' = f.fiberι t := by
        subst t'
        simp
      rw [Category.assoc, heq _ _ hbase]
      simp [q, tU, Scheme.Hom.fiberι]
    rw [← Scheme.Hom.comp_apply, hfst, Scheme.Hom.comp_apply]
    simp
  let e := ((f.fiber (f x.1)).presheaf.stalkCongr (.of_eq hpoint.symm) ≪≫
    asIso (q'.stalkMap ((f ∣_ U).asFiber x))).commRingCatIsoToRingEquiv
  rw [← ringKrullDim_eq_of_ringEquiv e, ← depth_eq_of_ringEquiv e]

private theorem isOpen_flat_stalks_spec
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    [LocallyOfFinitePresentation (Spec.map f)] :
    IsOpen {z : Spec S | ((Spec.map f).stalkMap z).hom.Flat} := by
  have hf : f.hom.FinitePresentation :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp inferInstance
  algebraize [f.hom]
  have : Algebra.FinitePresentation R S := hf
  have heq (z : PrimeSpectrum S) :
      ((Spec.map f).stalkMap z).hom.Flat ↔ Module.Flat R (Localization.AtPrime z.asIdeal) := by
    rw [RingHom.Flat.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso f z)]
    algebraize [Localization.localRingHom (z.comap f.hom).asIdeal z.asIdeal f.hom rfl]
    have : IsScalarTower R (Localization.AtPrime (z.comap f.hom).asIdeal)
        (Localization.AtPrime z.asIdeal) :=
      .of_algebraMap_eq fun r ↦ (Localization.localRingHom_to_map _ _ _ rfl r).symm
    change Module.Flat (Localization.AtPrime (z.comap f.hom).asIdeal)
      (Localization.AtPrime z.asIdeal) ↔ _
    exact Module.flat_iff_of_isLocalization
      (Localization.AtPrime (z.comap f.hom).asIdeal) (z.comap f.hom).asIdeal.primeCompl
      (Localization.AtPrime z.asIdeal)
  have hflat (z : PrimeSpectrum S) :
      Module.Flat R (Localization.AtPrime z.asIdeal) ↔
        Module.Flat R (LocalizedModule z.asIdeal.primeCompl S) := by
    let e := (IsLocalizedModule.iso z.asIdeal.primeCompl
      (Algebra.linearMap S (Localization.AtPrime z.asIdeal))).restrictScalars R
    exact ⟨fun h ↦ by
      let := h
      exact Module.Flat.of_linearEquiv e, fun h ↦ by
      let := h
      exact Module.Flat.of_linearEquiv e.symm⟩
  change IsOpen {z : PrimeSpectrum S | ((Spec.map f).stalkMap z).hom.Flat}
  simpa only [heq, hflat] using
    (Module.isOpen_setOf_flat_localizedModule (R := R) (S := S) (M := S))

private theorem isOpen_flat_stalks_affine
    {E L : Scheme.{u}} (p : E ⟶ L) [IsAffine E] [IsAffine L]
    [LocallyOfFinitePresentation p] :
    IsOpen {z : E | (p.stalkMap z).hom.Flat} := by
  let p' := E.isoSpec.inv ≫ p ≫ L.isoSpec.hom
  have h' : IsOpen {z : Spec Γ(E, ⊤) | (p'.stalkMap z).hom.Flat} := by
    have : LocallyOfFinitePresentation (Spec.map (Spec.preimage p')) := by
      rw [Spec.map_preimage]
      dsimp [p']
      infer_instance
    rw [← Spec.map_preimage p']
    exact isOpen_flat_stalks_spec _
  convert h'.preimage E.isoSpec.hom.continuous using 1
  ext z
  change (p.stalkMap z).hom.Flat ↔
    ((E.isoSpec.inv ≫ p ≫ L.isoSpec.hom).stalkMap (E.isoSpec.hom z)).hom.Flat
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_right_isIso, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_left_isIso]
  have he : E.isoSpec.inv (E.isoSpec.hom z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [he]

private theorem property_restrict_le
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {X T : Scheme.{u}} (f : X ⟶ T) {U V : T.Opens} (hVU : V ≤ U)
    (hf : P (f ∣_ U)) : P (f ∣_ V) := by
  have h := IsZariskiLocalAtTarget.restrict hf (U.ι ⁻¹ᵁ V)
  have heq : U.ι ''ᵁ U.ι ⁻¹ᵁ V = V := by
    rw [U.ι.image_preimage_eq_opensRange_inf]
    simpa using inf_eq_right.mpr hVU
  have h' := (P.arrow_mk_iso_iff (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mp h
  rwa [heq] at h'

set_option backward.isDefEq.respectTransparency false in
/-- The affine-base polynomial chart produced in the proof of Tag 00RH.

Proof: choose affine neighborhoods, apply quasi-finite polynomial factorization, use the
fibre flatness criterion and openness of flatness, and transport the resulting map to schemes.
Source: Stacks Project, Tag 00RH, using Tags 00QE, 00RE, 00R7 and 00RC.
(blueprint: lem-sbc-affine-base-flat-quasi-finite-chart-core) -/
theorem exists_affine_base_flat_quasiFinite_chart_core
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (y : X) (ht : f y ∈ U)
    (hdepth :
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ (n : ℕ) (O : X.Opens) (V : T.Opens)
      (_ : IsAffine V.toScheme)
      (e : O.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) V.toScheme),
      y ∈ O ∧ Flat e ∧ LocallyQuasiFinite e ∧ LocallyOfFinitePresentation e ∧
        e ≫ (AffineSpace (ULift.{u} (Fin n)) V.toScheme ↘ V.toScheme) ≫ V.ι =
          O.ι ≫ f := by
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset ht
  let _ : IsAffine V.toScheme := hV
  let g := f ∣_ V
  have : Flat g := property_restrict_le (@Flat) f hVU inferInstance
  have : LocallyOfFinitePresentation g :=
    property_restrict_le (@LocallyOfFinitePresentation) f hVU inferInstance
  let yV : (f ⁻¹ᵁ V).toScheme := ⟨y, hyV⟩
  have hdV := (fibre_depth_eq_ringKrullDim_restrict_iff f V yV).mpr hdepth
  obtain ⟨A, hA, hyA, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := (f ⁻¹ᵁ V).toScheme)
      (x := yV) (U := ⊤) (by trivial)
  let _ : IsAffine A.toScheme := hA
  let a : A.toScheme := ⟨yV, hyA⟩
  let k := A.ι ≫ g
  have hdk := (fibre_locus_source_iff A.ι g a).mpr hdV
  obtain ⟨B, hB, haB, n, e, hfp, hqf, he, hdim⟩ :=
    exists_quasiFinite_polynomial_chart k a
  let _ := hB
  let _ := hfp
  let _ := hqf
  let b : B.toScheme := ⟨a, haB⟩
  have hflat : (e.stalkMap b).hom.Flat :=
    (polynomial_chart_flat_stalk_iff_fibre_depth_and_dimension k B n e he b).mpr
      ⟨hdk, hdim⟩
  let W : B.toScheme.Opens := ⟨{z | (e.stalkMap z).hom.Flat},
    isOpen_flat_stalks_affine e⟩
  have : Flat (W.ι ≫ e) := by
    apply (Flat.iff_flat_stalkMap _).mpr
    intro z
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      RingHom.Flat.respectsIso.cancel_right_isIso]
    exact z.2
  let i := B.ι ≫ A.ι ≫ (f ⁻¹ᵁ V).ι
  let O := i ''ᵁ W
  let e' := (i.isoImage W).inv ≫ W.ι ≫ e
  refine ⟨n, O, V, hV, e', ?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · exact ⟨b, hflat, rfl⟩
  · dsimp [e', O]
    have he' := congrArg (fun t ↦ t ≫ V.ι) he
    simp only [Category.assoc] at he'
    simp only [Category.assoc]
    rw [he']
    simp only [k, g, Category.assoc, morphismRestrict_ι]
    simpa only [i, Category.assoc] using i.isoImage_inv_ι_assoc W f

end AlgebraicGeometry

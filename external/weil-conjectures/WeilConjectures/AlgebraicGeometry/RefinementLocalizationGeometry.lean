/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometry of the explicit common localization

Source: smooth purity blueprint, `sk-prop-sf-cbc`,
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-refinement-localization-geometry)
-/

@[expose] public section

set_option autoImplicit false
universe u v
open scoped TensorProduct
open AlgebraicGeometry

private theorem localized_factor_homeomorph
    (S C D T : Type u) [CommRing S] [CommRing C] [CommRing D] [CommRing T]
    [Algebra S C] [Algebra C D] [Algebra S D] [IsScalarTower S C D]
    [Algebra S T] (s : S) (hunit : IsUnit (algebraMap S T s))
    (hhomeo : (topologically IsHomeomorph).universally
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S C D)
          (AlgHom.id S (Localization.Away s))).toRingHom))) :
    let C' := T ⊗[S] C
    letI := Algebra.TensorProduct.rightAlgebra (R := S) (A := T) (B := C)
    (topologically IsHomeomorph).universally
      (Spec.map (CommRingCat.ofHom (algebraMap C' (C' ⊗[C] D)))) := by
  dsimp only
  let := Algebra.TensorProduct.rightAlgebra (R := S) (A := T) (B := C)
  let C' := T ⊗[S] C
  let E := C' ⊗[C] D
  let := Algebra.TensorProduct.rightAlgebra (R := C) (A := C') (B := D)
  let Cs := C ⊗[S] Localization.Away s
  let Ds := D ⊗[S] Localization.Away s
  let f : Cs →+* Ds :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S C D)
      (AlgHom.id S (Localization.Away s))).toRingHom
  let := f.toAlgebra
  have htower : IsScalarTower C Cs Ds := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change (algebraMap C D x) ⊗ₜ[S] (1 : Localization.Away s) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom S C D)
        (AlgHom.id S (Localization.Away s)) (x ⊗ₜ[S] 1)
    simp
  let := htower
  have hloc : IsLocalization.Away (algebraMap C D (algebraMap S C s)) Ds := by
    rw [← IsScalarTower.algebraMap_apply S C D]
    infer_instance
  let := hloc
  have hpush : Algebra.IsPushout C D Cs Ds := by
    apply Algebra.isPushout_of_isLocalization
      (Submonoid.powers (algebraMap S C s)) Cs D Ds
  let := hpush
  have top := CommRingCat.isPushout_of_isPushout C D Cs Ds
  have huC : IsUnit (algebraMap C C' (algebraMap S C s)) := by
    rw [← IsScalarTower.algebraMap_apply S C C', IsScalarTower.algebraMap_apply S T C']
    exact hunit.map (algebraMap T C')
  have hSD : IsScalarTower S D E := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply S C E, IsScalarTower.algebraMap_apply S C D,
      IsScalarTower.algebraMap_apply C D E]
  let := hSD
  have huD : IsUnit (algebraMap D E (algebraMap S D s)) := by
    rw [← IsScalarTower.algebraMap_apply S D E,
      IsScalarTower.algebraMap_apply S C' E]
    simpa only [← IsScalarTower.algebraMap_apply S C C'] using
      huC.map (algebraMap C' E)
  let q : Cs →+* C' := IsLocalization.Away.lift (algebraMap S C s) huC
  let p : Ds →+* E := IsLocalization.Away.lift (algebraMap S D s) huD
  have hq : q.comp (algebraMap C Cs) = algebraMap C C' := by
    simp [q]
  have hp : p.comp (algebraMap D Ds) = algebraMap D E := by
    simp [p]
  have hw : CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom f)
      (CommRingCat.ofHom p) = CategoryTheory.CategoryStruct.comp
        (CommRingCat.ofHom q) (CommRingCat.ofHom (algebraMap C' E)) := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap S C s))
    ext x
    change p (f (algebraMap C Cs x)) = algebraMap C' E (q (algebraMap C Cs x))
    change p (algebraMap Cs Ds (algebraMap C Cs x)) = _
    rw [← IsScalarTower.algebraMap_apply C Cs Ds]
    rw [IsScalarTower.algebraMap_apply C D Ds]
    simp only [p, q, IsLocalization.Away.lift_eq]
    exact (IsScalarTower.algebraMap_apply C D E x).symm.trans
      (IsScalarTower.algebraMap_apply C C' E x)
  have outer := (CommRingCat.isPushout_tensorProduct C C' D).flip
  have outer' : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap C D))
      (CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom (algebraMap C Cs))
        (CommRingCat.ofHom q))
      (CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom (algebraMap D Ds))
        (CommRingCat.ofHom p))
      (CommRingCat.ofHom (algebraMap C' E)) := by
    change CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap C D))
      (CommRingCat.ofHom (q.comp (algebraMap C Cs)))
      (CommRingCat.ofHom (p.comp (algebraMap D Ds)))
      (CommRingCat.ofHom (algebraMap C' E))
    rw [hq, hp]
    exact outer
  have lower := CategoryTheory.IsPushout.of_top outer' hw top
  exact CategoryTheory.MorphismProperty.of_isPullback
    (P := (topologically IsHomeomorph).universally)
    (isPullback_SpecMap_of_isPushout _ _ _ _ lower) hhomeo

/-- Source: smooth purity blueprint, sk-prop-sf-cbc,
lem-weil-pbc-finite-pushforward-generic-constructible, steps 4--9.
(blueprint: lem-weil-pbc-refinement-localization-geometry)

Proof: The product t of the nonzero s_j is nonzero in the domain S. Surjectivity
of Spec(C) -> Spec(S) makes S -> C injective: an element of the kernel belongs to
every prime ideal of S and hence is nilpotent, so is zero. The injective maps
C -> D_j then make the images of t nonzero in every D_j. C_T and E_j are the
localizations of C and D_j at the image of t, so the latter are domains.
Finiteness and etaleness of C_T over T, and finiteness of E_j over C_T, follow
by base change; the cover remains surjective by base change. Each s_j is a unit
in T since it divides t, so C_T -> E_j is also the base change of the given
universal homeomorphism over S[1/s_j]. Universal homeomorphisms persist under
base change and are surjective. Finally U -> T is an isomorphism by its
bijectivity, so the cover properties over T transport to U. No assertion about
a reduced tensor-product splitting is used or proved here. -/
theorem refinement_localization_geometry
    (S : Type u) [CommRing S] [IsDomain S]
    (C : Type u) [CommRing C] [IsDomain C] [Algebra S C]
    [Module.Finite S C] [Algebra.Etale S C]
    (hcover : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S C))))
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, IsDomain (D j)]
    [∀ j, Algebra C (D j)] [∀ j, Module.Finite C (D j)]
    (hinj : ∀ j, Function.Injective (algebraMap C (D j)))
    [∀ j, Algebra S (D j)] [∀ j, IsScalarTower S C (D j)]
    (s : Fin r → S) (hs : ∀ j, s j ≠ 0)
    (hhomeo : ∀ j, (topologically IsHomeomorph).universally
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S C (D j))
          (AlgHom.id S (Localization.Away (s j)))).toRingHom)))
    (T : Type u) [CommRing T] [Algebra S T]
    [IsLocalization.Away (∏ j, s j) T]
    (U : Type u) [CommRing U] [Algebra U T]
    (hUT : Function.Bijective (algebraMap U T)) :
    let C' := T ⊗[S] C
    letI := Algebra.TensorProduct.rightAlgebra (R := S) (A := T) (B := C)
    Module.Finite U C' ∧ Algebra.Etale U C' ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap U C'))) ∧
      ∀ j, Module.Finite C' (C' ⊗[C] D j) ∧ IsDomain (C' ⊗[C] D j) ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap C' (C' ⊗[C] D j)))) ∧
        (topologically IsHomeomorph).universally
          (Spec.map (CommRingCat.ofHom (algebraMap C' (C' ⊗[C] D j)))) := by
  dsimp only
  let := Algebra.TensorProduct.rightAlgebra (R := S) (A := T) (B := C)
  let C' := T ⊗[S] C
  have hSC : Function.Injective (algebraMap S C) := by
    apply (RingHom.injective_iff_ker_eq_bot _).mpr
    apply le_antisymm _ bot_le
    have hd : Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) := hcover.surj
    have hk := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp hd.denseRange
    simpa using hk
  have ht : (∏ j, s j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hs j)
  have hTC : Surjective (Spec.map (CommRingCat.ofHom (algebraMap T C'))) := by
    exact CategoryTheory.MorphismProperty.of_isPullback
      (P := @AlgebraicGeometry.Surjective)
      (isPullback_SpecMap_of_isPushout _ _ _ _
        (CommRingCat.isPushout_tensorProduct S T C)).flip hcover
  have hfiniteUT : Module.Finite U T :=
    Module.Finite.of_surjective (Algebra.linearMap U T) hUT.2
  let := hfiniteUT
  have hetaleUT : Algebra.Etale U T :=
    (RingHom.etale_algebraMap).mp (RingHom.Etale.of_bijective hUT)
  let := hetaleUT
  have hfinite : Module.Finite U C' := Module.Finite.trans T C'
  have hetale : Algebra.Etale U C' := Algebra.Etale.comp U T C'
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap U C'))) := by
    let e := RingEquiv.ofBijective (algebraMap U T) hUT
    let : CategoryTheory.IsIso (CommRingCat.ofHom (algebraMap U T)) :=
      e.toCommRingCatIso.isIso_hom
    let := hTC
    have h := (inferInstance : Surjective
      (CategoryTheory.CategoryStruct.comp
        (Spec.map (CommRingCat.ofHom (algebraMap T C')))
        (Spec.map (CommRingCat.ofHom (algebraMap U T)))))
    simpa only [← Spec.map_comp, CommRingCat.ofHom_comp,
      IsScalarTower.algebraMap_eq U T C'] using h
  refine ⟨hfinite, hetale, hsurj, fun j ↦ ?_⟩
  have hdomain : IsDomain (C' ⊗[C] D j) := by
    let := Algebra.TensorProduct.rightAlgebra (R := C) (A := C') (B := D j)
    have hloc : IsLocalization.Away (algebraMap C (D j) (algebraMap S C (∏ j, s j)))
        (C' ⊗[C] D j) := inferInstance
    exact IsLocalization.Away.isDomain _
      (map_ne_zero_iff _ (hinj j) |>.mpr (map_ne_zero_iff _ hSC |>.mpr ht))
  have hunit : IsUnit (algebraMap S T (s j)) :=
    IsLocalization.Away.isUnit_of_dvd (S := T) (∏ j, s j)
      (Finset.dvd_prod_of_mem s (Finset.mem_univ j))
  have hh := localized_factor_homeomorph S C (D j) T (s j) hunit (hhomeo j)
  have hsurjFactor : Surjective
      (Spec.map (CommRingCat.ofHom (algebraMap C' (C' ⊗[C] D j)))) :=
    ⟨((CategoryTheory.MorphismProperty.universally_le
      (topologically IsHomeomorph)) _ hh).surjective⟩
  exact ⟨inferInstance, hdomain, hsurjFactor, hh⟩

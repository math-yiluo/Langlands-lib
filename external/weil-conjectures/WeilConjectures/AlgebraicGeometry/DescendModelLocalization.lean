/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Spec
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Algebra.Shrink

/-!
# DescendModelLocalization

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9.
(blueprint: lem-weil-pbc-descend-model-localization)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open AlgebraicGeometry

private theorem shrink_scalarTower
    (R B C : Type*) [CommSemiring R] [CommSemiring B] [Semiring C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    [Small.{u} C] : IsScalarTower R B (Shrink.{u} C) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply (Shrink.ringEquiv C).injective
  change (Shrink.algEquiv R C) (algebraMap R (Shrink C) x) =
    (Shrink.algEquiv B C) (algebraMap B (Shrink C) (algebraMap R B x))
  rw [(Shrink.algEquiv R C).commutes, (Shrink.algEquiv B C).commutes,
    ← IsScalarTower.algebraMap_apply R B C]

/-- Transport a finite étale localization to a small ring, preserving its scalar towers. -/
private theorem exists_small_localization_model
    (A R : Type u) (A0 T K' : Type*)
    [CommRing A] [CommRing R] [CommRing A0] [CommRing T] [Field K']
    [Algebra A R] [Algebra A A0] [Algebra A T] [Algebra R T]
    [Algebra A0 T] [Algebra A0 K'] [Algebra T K']
    [IsScalarTower A R T] [IsScalarTower A A0 T] [IsScalarTower A0 T K']
    [IsDomain T] [Module.Finite R T] [Algebra.Etale R T] [IsFractionRing T K']
    (s : A0) [IsLocalization.Away s T]
    (hinj : Function.Injective (algebraMap R T)) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra R A')
      (_ : Algebra A A') (_ : IsScalarTower A R A')
      (_ : IsDomain A') (_ : Algebra A' K') (_ : Algebra A0 A')
      (_ : IsScalarTower A A0 A') (_ : IsScalarTower A0 A' K')
      (_ : IsLocalization.Away s A'),
      Module.Finite R A' ∧ Algebra.Etale R A' ∧ IsFractionRing A' K' ∧
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A'))) := by
  have : Small.{u} T := Module.Finite.small R T
  let A' := Shrink.{u} T
  let : Algebra A' K' :=
    ((algebraMap T K').comp (Shrink.ringEquiv T).toRingHom).toAlgebra
  have : IsScalarTower A R A' := shrink_scalarTower A R T
  have : IsScalarTower A A0 A' := shrink_scalarTower A A0 T
  have : IsScalarTower A0 A' K' := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap A0 K' x =
      algebraMap T K' ((Shrink.algEquiv A0 T) (algebraMap A0 A' x))
    rw [(Shrink.algEquiv A0 T).commutes, ← IsScalarTower.algebraMap_apply A0 T K']
  have : IsLocalization.Away s A' :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers s)
      (Shrink.algEquiv A0 T).symm
  have : Module.Finite R A' := inferInstance
  have : Algebra.Etale R A' := Algebra.Etale.of_equiv (Shrink.algEquiv R T).symm
  have : IsFractionRing A' K' :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
      (S := K') (Shrink.ringEquiv T).symm).mp inferInstance
  refine ⟨A', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hRA' : Function.Injective (algebraMap R A') := by
    intro x y h
    apply hinj
    have h' := congrArg (Shrink.algEquiv R T) h
    exact (Shrink.algEquiv R T).commutes x ▸
      (Shrink.algEquiv R T).commutes y ▸ h'
  have : FaithfulSMul R A' := (faithfulSMul_iff_algebraMap_injective R A').mpr hRA'
  exact ⟨Algebra.IsIntegral.comap_surjective R A'⟩

/-- Localize a finite étale algebra along an injective map from a localized base. -/
private theorem exists_base_element_model_localization_of_injective
    (A : Type u) [CommRing A] [IsDomain A]
    (S0 A0 K' : Type*) [CommRing S0] [CommRing A0] [IsDomain A0] [Field K']
    [Algebra A S0] [Algebra A A0] [Algebra S0 A0] [Algebra A0 K']
    [IsScalarTower A S0 A0]
    (c0 : A) (hc0 : c0 ≠ 0) [IsLocalization.Away c0 S0]
    [Module.Finite S0 A0] [Algebra.Etale S0 A0] [IsFractionRing A0 K']
    (hS0 : Function.Injective (algebraMap S0 A0)) (a : S0) (ha : a ≠ 0) :
      ∃ (c : A) (A' : Type u) (_ : CommRing A') (_ : Algebra (Localization.Away c) A')
        (_ : Algebra A A') (_ : IsScalarTower A (Localization.Away c) A')
        (_ : IsDomain A') (_ : Algebra A' K') (_ : Algebra A0 A')
        (_ : IsScalarTower A A0 A') (_ : IsScalarTower A0 A' K')
        (_ : IsLocalization.Away (algebraMap S0 A0 a) A'),
        c ≠ 0 ∧ Module.Finite (Localization.Away c) A' ∧
          Algebra.Etale (Localization.Away c) A' ∧ IsFractionRing A' K' ∧
          Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A')))
    := by
  let s := algebraMap S0 A0 a
  let S := Localization.Away a
  let T := Localization.Away s
  have hs : s ≠ 0 := fun h ↦ ha (hS0 (by simpa [s] using h))
  let : IsDomain T := Localization.Away.isDomain hs
  let : Algebra S T :=
    (IsLocalization.Away.map S T (algebraMap S0 A0) a).toAlgebra
  have : IsScalarTower S0 S T := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap S0 T x =
      IsLocalization.Away.map S T (algebraMap S0 A0) a (algebraMap S0 S x)
    symm
    exact IsLocalization.map_eq (M := Submonoid.powers a) (S := S)
      (Q := T) (g := algebraMap S0 A0) _ x
  have : Module.Finite S T := Module.Finite.of_isLocalization S0 A0 (Submonoid.powers a)
  have : Algebra.Etale A0 T := Algebra.Etale.of_isLocalizationAway s
  have : Algebra.Etale S0 T := Algebra.Etale.comp S0 A0 T
  let : Algebra T K' :=
    (IsLocalization.Away.lift (S := T) (g := algebraMap A0 K') s
      (isUnit_iff_ne_zero.mpr (fun h ↦
        hs (IsFractionRing.injective A0 K' (by simpa using h))))).toAlgebra
  have : IsScalarTower A0 T K' := by
    apply IsScalarTower.of_algebraMap_eq'
    symm
    exact IsLocalization.Away.lift_comp _ _
  have : IsFractionRing T K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers s) T K'
  let b := (IsLocalization.Away.sec c0 a).1
  have hb : b ≠ 0 := by
    intro h
    have h' := IsLocalization.Away.associated_sec_fst c0 a
    have : Associated (0 : S0) a := by simpa [b, h] using h'
    exact ha (this.eq_zero_iff.mp rfl)
  let c := c0 * b
  have hc : c ≠ 0 := mul_ne_zero hc0 hb
  have : IsLocalization.Away c S :=
    IsLocalization.Away.mul_of_associated c0 b a
      (IsLocalization.Away.associated_sec_fst c0 a)
  let R := Localization.Away c
  let e := IsLocalization.algEquiv (Submonoid.powers c) S R
  let : Algebra R T := ((algebraMap S T).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower A S0 T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rw [IsScalarTower.algebraMap_apply A A0 T,
      IsScalarTower.algebraMap_apply A S0 A0,
      ← IsScalarTower.algebraMap_apply S0 A0 T]
  have : IsScalarTower A S T := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp only [RingHom.comp_apply, IsScalarTower.algebraMap_apply A S0 S,
      IsScalarTower.algebraMap_apply S0 S T,
      IsScalarTower.algebraMap_apply A S0 T]
  have : IsScalarTower A R T := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap A T x = algebraMap S T (e.symm (algebraMap A R x))
    rw [e.symm.commutes, ← IsScalarTower.algebraMap_apply A S T]
  have : Module.Finite R T :=
    Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl T) (by
      ext x
      change algebraMap S T (e.symm (e x)) = algebraMap S T x
      rw [e.symm_apply_apply])
  have : Algebra.Etale A S0 := Algebra.Etale.of_isLocalizationAway c0
  have : Algebra.Etale A T := Algebra.Etale.comp A S0 T
  have : Algebra.Etale A R := Algebra.Etale.of_isLocalizationAway c
  have : Algebra.Etale R T := Algebra.Etale.of_restrictScalars A R T
  have hST : Function.Injective (algebraMap S T) := by
    apply (IsLocalization.Away.map_injective_iff (S := S) (Q := T)
      (algebraMap S0 A0) a).mpr
    intro x hx
    refine ⟨0, ?_⟩
    have : x = 0 := hS0 (by simpa using hx)
    simp [this]
  have hRT : Function.Injective (algebraMap R T) := hST.comp e.symm.injective
  obtain ⟨A', hA', hR, hA, hAR, hdom, hK, h0, hA0, h0K, hloc, hprops⟩ :=
    exists_small_localization_model A R A0 T K' s hRT
  exact ⟨c, A', hA', hR, hA, hAR, hdom, hK, h0, hA0, h0K, hloc,
    hc, hprops⟩

set_option backward.isDefEq.respectTransparency false in
/-- Core construction of a nonzero localization of a finite étale model.

The proof follows the denominator-clearing and localization argument in the
smooth purity blueprint, `lem-weil-pbc-finite-pushforward-generic-constructible`,
steps 4--9. Write the base element as a fraction with numerator `b`. The
localization at this element is also the localization of `A` at `c0 * b`.
Localize `A0` at its image, use the finite-module localization theorem, and
transport along the base localization equivalence. The localization remains
étale by composition and restriction of scalars, and has fraction field `K'`.
Its finite module structure over `A[1/(c0*b)]` proves smallness. Shrink the ring
and transport the algebra maps and their scalar towers through the resulting
ring equivalence. Finally apply integral lying over to the injective base map.
(blueprint: lem-weil-pbc-descend-model-localization)
-/
private theorem exists_base_element_model_localization
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (K' : Type (max u v)) [Field K'] [Algebra A K']
    (c0 : A) (hc0 : c0 ≠ 0) (S0 : Subalgebra A K')
    [IsLocalization.Away c0 S0] (A0 : Subalgebra S0 K')
    [Algebra A A0] [IsScalarTower A S0 A0] [IsScalarTower A A0 K']
    [Module.Finite S0 A0] [Algebra.Etale S0 A0] [IsFractionRing A0 K']
    (_hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S0 A0))))
    (a : S0) (ha : a ≠ 0) :
      ∃ (c : A) (A' : Type u) (_ : CommRing A') (_ : Algebra (Localization.Away c) A')
        (_ : Algebra A A') (_ : IsScalarTower A (Localization.Away c) A')
        (_ : IsDomain A') (_ : Algebra A' K') (_ : Algebra A0 A')
        (_ : IsScalarTower A A0 A') (_ : IsScalarTower A0 A' K')
        (_ : IsLocalization.Away (algebraMap S0 A0 a) A'),
        c ≠ 0 ∧ Module.Finite (Localization.Away c) A' ∧
          Algebra.Etale (Localization.Away c) A' ∧ IsFractionRing A' K' ∧
          Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A')))
    := by
  have hS0 : Function.Injective (algebraMap S0 A0) := by
    intro x y h
    apply Subtype.ext
    change algebraMap S0 K' x = algebraMap S0 K' y
    simpa only [IsScalarTower.algebraMap_apply S0 A0 K'] using
      congrArg (algebraMap A0 K') h
  exact exists_base_element_model_localization_of_injective A S0 A0 K' c0 hc0 hS0 a ha

/-- Descend a specified nonzero denominator of a finite étale domain model to a
principal open of the original base. The resulting small domain is a localization of
that model at a multiple of the denominator. No finite algebra B or product of fields
occurs in this statement.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`, steps 4--9; steps 3--4 of
`lem-weil-pbc-spread-generic-product-embedding`.
(blueprint: lem-weil-pbc-descend-model-localization)

Proof: The nonzero t is integral over S0 because A0 is finite over S0. Among its
monic integral equations choose one of least degree. Its constant coefficient a is
nonzero: otherwise cancel t in the domain and obtain a monic equation of smaller
degree. Evaluating the equation shows that the image of a is divisible by t in A0.
Write a = b/c0^n in S0 with b nonzero in A. Put c = c0*b and s = algebraMap S0 A0 a.
Localizing S0 at a is the same as localizing A at c. Localizing A0 at s is consequently
the base change of A0 along that localization of S0. Hence it remains finite étale
and surjective on spectra. It remains a domain and has fraction field K', since s
is nonzero. It is finite as a module over A[1/c], so it is small in the universe of A.
Transport its ring, algebras, localization and fraction-ring structures to a small
presentation. The algebra maps from A0, A and A[1/c], and the map to K', commute by
construction; they give all the displayed scalar towers. -/
theorem exists_descend_model_localization
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    (K' : Type (max u v)) [Field K'] [Algebra A K']
    (c0 : A) (hc0 : c0 ≠ 0) (S0 : Subalgebra A K')
    [IsLocalization.Away c0 S0] (A0 : Subalgebra S0 K')
    [Algebra A A0] [IsScalarTower A S0 A0] [IsScalarTower A A0 K']
    [Module.Finite S0 A0] [Algebra.Etale S0 A0] [IsFractionRing A0 K']
    (hsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap S0 A0))))
    (t : A0) (ht : t ≠ 0) :
    ∃ (s : A0), t ∣ s ∧ s ≠ 0 ∧
      ∃ (c : A) (A' : Type u) (_ : CommRing A') (_ : Algebra (Localization.Away c) A')
        (_ : Algebra A A') (_ : IsScalarTower A (Localization.Away c) A')
        (_ : IsDomain A') (_ : Algebra A' K') (_ : Algebra A0 A')
        (_ : IsScalarTower A A0 A') (_ : IsScalarTower A0 A' K')
        (_ : IsLocalization.Away s A'),
        c ≠ 0 ∧ Module.Finite (Localization.Away c) A' ∧
          Algebra.Etale (Localization.Away c) A' ∧ IsFractionRing A' K' ∧
          Surjective (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A')))
          := by
  obtain ⟨a, ha, hta⟩ :=
    (IsIntegral.of_finite (R := S0) t).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_iff_ne_zero.mpr ht)
  have hinj : Function.Injective (algebraMap S0 A0) := by
    intro x y h
    apply Subtype.ext
    change algebraMap S0 K' x = algebraMap S0 K' y
    simpa only [IsScalarTower.algebraMap_apply S0 A0 K'] using
      congrArg (algebraMap A0 K') h
  refine ⟨algebraMap S0 A0 a, hta, ?_, ?_⟩
  · exact fun h ↦ ha (hinj (by simpa using h))
  · exact exists_base_element_model_localization A K' c0 hc0 S0 A0 hsurj a ha


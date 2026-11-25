/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import WeilConjectures.RingTheory.FiniteLengthGlobalSubmodule
import WeilConjectures.RingTheory.KrullAkizukiNoetherian
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp

/-!
# Integral closure of a one-dimensional Noetherian domain

Source: literature/stacks-project/algebra.tex, Algebra Lemma 09IG
(blueprint: lem-sc-integral-closure-dedekind-surjective-fibres).
-/

@[expose] public section

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Transport finiteness along the canonical affine stalk isomorphisms. -/
private theorem finite_spec_residueFieldMap {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (x : PrimeSpectrum S)
    (h : (Ideal.ResidueField.map (x.comap φ.hom).asIdeal x.asIdeal φ.hom rfl).Finite) :
    ((Spec.map φ).residueFieldMap x).hom.Finite := by
  have : IsLocalHom (Spec.stalkIso S x).inv.hom :=
    isLocalHom_of_iso (Spec.stalkIso S x).symm
  have : IsLocalHom (Spec.stalkIso R (x.comap φ.hom)).hom.hom :=
    isLocalHom_of_iso (Spec.stalkIso R (x.comap φ.hom))
  change (IsLocalRing.ResidueField.map ((Spec.map φ).stalkMap x).hom).Finite
  simp only [← Scheme.localRingHom_comp_stalkIso φ x, CommRingCat.hom_comp,
    CommRingCat.hom_ofHom]
  rw [IsLocalRing.ResidueField.map_comp, IsLocalRing.ResidueField.map_comp]
  apply RingHom.Finite.comp
  · exact (RingHom.Finite.of_surjective _ (IsLocalRing.ResidueField.mapEquiv
      (Spec.stalkIso S x).symm.commRingCatIsoToRingEquiv).surjective).comp h
  · exact RingHom.Finite.of_surjective _ (IsLocalRing.ResidueField.mapEquiv
      (Spec.stalkIso R (x.comap φ.hom)).commRingCatIsoToRingEquiv).surjective

private theorem isFractionRing_residueField_of_eq_bot
    {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] (hp : p = ⊥) :
    IsFractionRing R p.ResidueField := by
  subst p
  infer_instance

/-- The same finite extension expressed using different fraction fields is finite. -/
private theorem finite_fractionRingMap
    {A C K L F E : Type*} [CommRing A] [IsDomain A] [CommRing C] [IsDomain C]
    [Field K] [Field L] [Field F] [Field E]
    [Algebra A K] [IsFractionRing A K] [Algebra C L] [IsFractionRing C L]
    [Algebra A C] [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A C L] [IsScalarTower A K L]
    [Algebra A F] [IsFractionRing A F] [Algebra C E] [IsFractionRing C E]
    (φ : F →+* E)
    (hφ : ∀ a, φ (algebraMap A F a) = algebraMap C E (algebraMap A C a)) :
    φ.Finite := by
  let eA := IsLocalization.algEquiv (nonZeroDivisors A) F K
  let eC := IsLocalization.algEquiv (nonZeroDivisors C) L E
  have heq : φ = eC.toRingHom.comp ((algebraMap K L).comp eA.toRingHom) := by
    apply IsFractionRing.ringHom_ext (A := A)
    intro a
    change φ (algebraMap A F a) = eC (algebraMap K L (eA (algebraMap A F a)))
    rw [hφ, eA.commutes]
    rw [← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A C L]
    exact (eC.commutes _).symm
  rw [heq]
  exact (RingHom.Finite.of_surjective _ eC.surjective).comp
    ((RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite K L)).comp
      (RingHom.Finite.of_surjective _ eA.surjective))

open scoped Pointwise in
/-- Stacks Tag 00PF makes a closed residue field a quotient of a finite-length module. -/
private theorem finite_residueFieldMap_of_nonzero_comap
    {A C K L : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing C] [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A C] [Algebra C L]
    [Algebra A L] [IsScalarTower A K L] [IsScalarTower A C L]
    (hCL : Function.Injective (algebraMap C L)) (hA : ringKrullDim A = 1)
    (q : Ideal C) [q.IsMaximal] (hp : q.comap (algebraMap A C) ≠ ⊥) :
    (Ideal.ResidueField.map (q.comap (algebraMap A C)) q (algebraMap A C) rfl).Finite := by
  classical
  obtain ⟨a, ha, ha0⟩ := (q.comap (algebraMap A C)).ne_bot_iff.mp hp
  let j : C →ₗ[A] (Fin (Module.finrank K L) → K) :=
    ((Module.finBasis K L).equivFun.restrictScalars A).toLinearMap.comp
      ((Algebra.linearMap C L).restrictScalars A)
  have hj : Function.Injective j :=
    (Module.finBasis K L).equivFun.injective.comp hCL
  let e := LinearEquiv.ofInjective j hj
  have hlen : Module.length A (QuotSMulTop a C) < ⊤ := by
    rw [(QuotSMulTop.congr a e).length_eq]
    exact Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one
      (Module.finrank K L) (LinearMap.range j) hA a ha0
  have : _root_.IsNoetherian A (QuotSMulTop a C) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (Module.length_ne_top_iff.mp hlen.ne)).1
  let r : C →ₗ[A] q.ResidueField := (Algebra.linearMap C q.ResidueField).restrictScalars A
  have hr : a • (⊤ : Submodule A C) ≤ LinearMap.ker r := by
    intro z hz
    obtain ⟨w, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
    change algebraMap C q.ResidueField (a • w) = 0
    rw [Algebra.smul_def, map_mul, Ideal.algebraMap_residueField_eq_zero.mpr
      (show algebraMap A C a ∈ q from ha), zero_mul]
  let r' : QuotSMulTop a C →ₗ[A] q.ResidueField := (a • (⊤ : Submodule A C)).liftQ r hr
  have : Module.Finite A q.ResidueField := Module.Finite.of_surjective r' (by
    intro z
    obtain ⟨w, hw⟩ := Ideal.algebraMap_residueField_surjective q z
    exact ⟨Submodule.Quotient.mk w, hw⟩)
  let φ := Ideal.ResidueField.map (q.comap (algebraMap A C)) q (algebraMap A C) rfl
  let : Algebra (q.comap (algebraMap A C)).ResidueField q.ResidueField := φ.toAlgebra
  have : IsScalarTower A (q.comap (algebraMap A C)).ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      exact (Ideal.ResidueField.map_algebraMap _ _ _ _ a).symm)
  exact Module.Finite.of_restrictScalars_finite A _ _

/-- The integral closure of a one-dimensional Noetherian domain in a finite field
extension is Dedekind, and its spectrum maps surjectively with finite fibres and
finite residue-field extensions (Stacks, Algebra Lemma 09IG).

Proof (Stacks, Algebra Lemma 09IG, `lemma-integral-closure-Dedekind`):
1. Since `A ⊆ C ⊆ L`, Krull--Akizuki gives Noetherianity of `C`
   (`lem-sc-krull-akizuki-noetherian`).
2. The integral injective inclusion preserves dimension, giving `dim C = 1`
   (`lem-weil-pbc-integral-injective-dimension-equal`). The integral closure is a
   normal domain with fraction field `L`
   (`lem-weil-pbc-integral-closure-finite-extension-normal`), hence is Dedekind.
3. Lying over for the integral injective inclusion gives surjectivity on spectra
   (`lem-weil-pbc-integral-injective-lying-over`).
4. At each nonzero prime of `A`, dimension one gives maximality, and Mathlib's
   `IsDedekindDomain.primesOver_finite` gives finitely many primes of `C` above it.
   Mathlib's `Ideal.eq_bot_of_comap_eq_bot` leaves only the zero ideal in the
   fibre over zero.
5. For a closed prime `q` of `C` above `p`, choose nonzero `a ∈ p`. A finite
   `K`-basis of `L` embeds `C` as an `A`-submodule of a finite power of `K`.
   The global finite-length lemma (Stacks Tag 00PF,
   `lem-sc-finite-length-global-submodule`) gives finite length of `C/aC`.
   The surjection `C → κ(q)` factors through `C/aC`, hence `κ(q)` is finite
   over `A`, and therefore over `κ(p)` via the canonical residue-field map.
   At zero, the residue fields are fraction fields; their map is conjugate to
   the given finite extension `K → L`. The canonical stalk isomorphisms
   identify these ideal residue-field maps with the scheme residue-field maps.

Mathlib's Dedekind predicate permits dimension zero, so dimension one is stated
separately to retain the node's convention.
(blueprint: lem-sc-integral-closure-dedekind-surjective-fibres).
-/
theorem integralClosure_isDedekind_surjective_finite_fibres
    (A L : Type u) (K : Type v) [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [IsNoetherianRing A]
    (hA : ringKrullDim A = 1) :
    let C := integralClosure A L
    let f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A C))
    IsDedekindDomain C ∧ ringKrullDim C = 1 ∧ Function.Surjective f.base ∧
      (∀ y : Spec (CommRingCat.of A), Finite (f ⁻¹' {y})) ∧
      (∀ x : Spec (CommRingCat.of C), (f.residueFieldMap x).hom.Finite) := by
  dsimp only
  let C := integralClosure A L
  have hAC : Function.Injective (algebraMap A C) := by
    apply Function.Injective.of_comp (f := algebraMap C L)
    change Function.Injective ((algebraMap C L).comp (algebraMap A C))
    rw [← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).mpr hAC
  have : IsNoetherianRing C := krullAkizukiNoetherian (K := K) (L := L)
    hAC (IsIntegralClosure.algebraMap_injective C A L) hA
  have hC : ringKrullDim C = 1 := (ringKrullDim_eq_of_isIntegral A C).trans hA
  have : Ring.KrullDimLE 1 C := Ring.krullDimLE_iff.mpr hC.le
  have : Ring.DimensionLEOne C := ⟨fun hp hprime ↦ hprime.isMaximal_of_ne_bot hp⟩
  have : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hDed : IsDedekindDomain C :=
    { (inferInstance : IsNoetherianRing C),
      (inferInstance : Ring.DimensionLEOne C),
      (inferInstance : IsIntegrallyClosed C) with }
  refine ⟨hDed, hC, ?_, ?_, ?_⟩
  · exact Algebra.IsIntegral.comap_surjective A C
  · intro y
    have : IsDedekindDomain C := hDed
    have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hA.le
    let g := PrimeSpectrum.comap (algebraMap A C)
    have hf : Set.Finite (g ⁻¹' {y}) := by
      by_cases hy : y.asIdeal = ⊥
      · apply Set.Subsingleton.finite
        intro x hx z hz
        apply PrimeSpectrum.ext
        have hx0 : x.asIdeal = ⊥ := Ideal.eq_bot_of_under_eq_bot
          ((congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hx)).trans hy)
        have hz0 : z.asIdeal = ⊥ := Ideal.eq_bot_of_under_eq_bot
          ((congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hz)).trans hy)
        exact hx0.trans hz0.symm
      · have : y.asIdeal.IsMaximal := y.isPrime.isMaximal_of_ne_bot hy
        apply (IsDedekindDomain.primesOver_finite y.asIdeal C).preimage
          (fun _ _ _ _ h ↦ PrimeSpectrum.ext h) |>.subset
        intro x hx
        refine ⟨x.isPrime, ⟨?_⟩⟩
        exact (congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hx)).symm
    exact hf.to_subtype
  · intro x
    change PrimeSpectrum C at x
    apply finite_spec_residueFieldMap
    have : IsDedekindDomain C := hDed
    have : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
    let q := x.asIdeal
    change (Ideal.ResidueField.map (q.comap (algebraMap A C)) q
      (algebraMap A C) rfl).Finite
    by_cases hp : q.comap (algebraMap A C) = ⊥
    · have hq : q = ⊥ := Ideal.eq_bot_of_under_eq_bot hp
      have : IsFractionRing C q.ResidueField := isFractionRing_residueField_of_eq_bot q hq
      have : IsFractionRing A (q.comap (algebraMap A C)).ResidueField :=
        isFractionRing_residueField_of_eq_bot _ hp
      exact finite_fractionRingMap (K := K) (L := L) _
        (Ideal.ResidueField.map_algebraMap _ _ _ _)
    · have hq : q ≠ ⊥ := by
        intro hq
        apply hp
        rw [hq, Ideal.comap_bot_of_injective _ hAC]
      have : q.IsMaximal := x.isPrime.isMaximal hq
      exact finite_residueFieldMap_of_nonzero_comap (K := K) (L := L)
        (IsIntegralClosure.algebraMap_injective C A L) hA q hp

end AlgebraicGeometry

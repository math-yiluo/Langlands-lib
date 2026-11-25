/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Integral

/-!
# A monic separable polynomial model after principal localization

Source: Stacks Project, Algebra, Tag 00UB, denominator-clearing calculation in
`lem-weil-pbc-spread-finite-separable-extension`.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
namespace AlgebraicGeometry

private theorem polynomial_lift_of_integer_normalization
    {A K S : Type*} [CommRing A] [Field K] [CommRing S]
    [Algebra A K] [IsFractionRing A K] [Algebra A S]
    (φ : S →+* K) (hφ : φ.comp (algebraMap A S) = algebraMap A K)
    (p : Polynomial K) (b : A)
    (hn : (IsLocalization.integerNormalization (nonZeroDivisors A) p).map
      (algebraMap A K) = b • p)
    (hb : IsUnit (algebraMap A S b)) : ∃ q : Polynomial S, q.map φ = p := by
  obtain ⟨r, hr⟩ := isUnit_iff_exists_inv.mp hb
  refine ⟨Polynomial.C r *
    (IsLocalization.integerNormalization (nonZeroDivisors A) p).map (algebraMap A S), ?_⟩
  have hprod : φ r * algebraMap A K b = 1 := by
    have h := congrArg φ hr
    simpa only [map_mul, map_one, ← RingHom.comp_apply, hφ, mul_comm] using h
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, hφ, hn,
    ← algebraMap_smul K b p, Polynomial.smul_eq_C_mul, ← mul_assoc,
    ← Polynomial.C_mul, hprod, Polynomial.C_1, one_mul]

/-- An integral element with separable minimal polynomial has a monogenic polynomial model
with invertible derivative after localizing the base domain. No assertion is made that the
ambient field is the fraction field of this monogenic algebra.

Source: Stacks Project, Algebra, Tag 00UB, denominator-clearing calculation in the proof of
`lem-weil-pbc-spread-finite-separable-extension`.
(blueprint: lem-weil-pbc-localized-separable-polynomial-model)

Proof: Write the coefficients of the monic minimal polynomial p as fractions over A.
Since p is separable, choose a Bezout identity u*p + v*p' = 1 over K. Include the
coefficients of u and v in the finite list of fractions. Let c be the product of their
nonzero denominators, and let S be the image of A[1/c] in L under the canonical injective
map. The localization identifies S with A[1/c]. All the listed coefficients lie in S;
thus p descends to a monic polynomial f over S, and its Bezout identity proves that f and
f' are coprime. The canonical localization map into K identifies S with a subring of K;
its composition into L is the given inclusion, and coefficientwise mapping sends f to p. -/
theorem exists_localized_separable_polynomial_model
    (A : Type u) [CommRing A] [IsDomain A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (α : L) (hα : IsIntegral K α) (hsep : (minpoly K α).Separable) :
    ∃ c : A, c ≠ 0 ∧ ∃ S : Subalgebra A L,
      IsLocalization.Away c S ∧ ∃ φ : S →+* K,
        (algebraMap K L).comp φ = algebraMap S L ∧ ∃ f : Polynomial S,
          f.Monic ∧ IsCoprime f f.derivative ∧ f.map φ = minpoly K α := by
  classical
  obtain ⟨u, v, huv⟩ := (Polynomial.separable_def _).mp hsep
  obtain ⟨b₁, hb₁, hn₁⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors A) (minpoly K α)
  obtain ⟨b₂, hb₂, hn₂⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) u
  obtain ⟨b₃, hb₃, hn₃⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) v
  let c := b₁ * b₂ * b₃
  have hc : c ≠ 0 := mul_ne_zero
    (mul_ne_zero (nonZeroDivisors.ne_zero hb₁) (nonZeroDivisors.ne_zero hb₂))
    (nonZeroDivisors.ne_zero hb₃)
  let D := Localization.Away c
  have hunitK : IsUnit (algebraMap A K c) :=
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hc)
  let kmap : D →ₐ[A] K := IsLocalization.Away.liftAlgHom c (f := Algebra.ofId A K) hunitK
  have hkmap : Function.Injective kmap := by
    change Function.Injective (IsLocalization.Away.lift c hunitK)
    apply (IsLocalization.lift_injective_iff _).mpr
    intro x y
    constructor
    · intro h
      exact congrArg (algebraMap A K)
        (IsLocalization.injective D (powers_le_nonZeroDivisors_of_noZeroDivisors hc) h)
    · intro h
      exact congrArg (algebraMap A D) ((IsFractionRing.injective A K) h)
  let lmap : D →ₐ[A] L := (IsScalarTower.toAlgHom A K L).comp kmap
  have hlmap : Function.Injective lmap := (algebraMap K L).injective.comp hkmap
  let S : Subalgebra A L := lmap.range
  let e : D ≃ₐ[A] S := AlgEquiv.ofBijective lmap.rangeRestrict
    ⟨fun x y h ↦ hlmap (congrArg Subtype.val h), lmap.rangeRestrict_surjective⟩
  have hS : IsLocalization.Away c S :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers c) e
  let φ : S →+* K := kmap.toRingHom.comp e.symm.toRingHom
  have hφ : (algebraMap K L).comp φ = algebraMap S L := by
    ext s
    change lmap (e.symm s) = (s : L)
    exact congrArg Subtype.val (e.apply_symm_apply s)
  have hφA : φ.comp (algebraMap A S) = algebraMap A K := by
    ext a
    change kmap (e.symm (algebraMap A S a)) = algebraMap A K a
    rw [e.symm.commutes, kmap.commutes]
  have hinjφ : Function.Injective φ := hkmap.comp e.symm.injective
  have hunitS : IsUnit (algebraMap A S c) := by
    let := hS
    exact IsLocalization.Away.algebraMap_isUnit c
  have hunit₁ : IsUnit (algebraMap A S b₁) := by
    exact isUnit_of_mul_isUnit_left
      (isUnit_of_mul_isUnit_left (by simpa only [c, map_mul] using hunitS))
  have hunit₂ : IsUnit (algebraMap A S b₂) := by
    exact isUnit_of_mul_isUnit_right
      (isUnit_of_mul_isUnit_left (by simpa only [c, map_mul] using hunitS))
  have hunit₃ : IsUnit (algebraMap A S b₃) := by
    exact isUnit_of_mul_isUnit_right (by simpa only [c, map_mul] using hunitS)
  obtain ⟨f, hf⟩ := polynomial_lift_of_integer_normalization φ hφA _ b₁ hn₁ hunit₁
  obtain ⟨uS, huS⟩ := polynomial_lift_of_integer_normalization φ hφA u b₂ hn₂ hunit₂
  obtain ⟨vS, hvS⟩ := polynomial_lift_of_integer_normalization φ hφA v b₃ hn₃ hunit₃
  refine ⟨c, hc, S, hS, φ, hφ, f, ?_, ?_, hf⟩
  · exact Polynomial.monic_of_injective hinjφ (hf.symm ▸ minpoly.monic hα)
  · refine ⟨uS, vS, ?_⟩
    apply Polynomial.map_injective φ hinjφ
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
      ← Polynomial.derivative_map, hf, huS, hvS] using huv

end AlgebraicGeometry

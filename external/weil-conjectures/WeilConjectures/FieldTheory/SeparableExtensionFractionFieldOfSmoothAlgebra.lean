/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.RingTheory.SmoothAtGenericPointOverField

/-!
# A separable extension as the fraction field of a smooth algebra

Source: Stacks Project, Algebra, Lemma Tag 037X (lemma-localization-smooth-separable),
implication “separable => localization of a smooth k-algebra” (blueprint:
lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra).
-/

@[expose] public section

universe u v

namespace FieldTheory

/-- Let `K/k` be a field extension finitely generated as a field (`(⊤ : IntermediateField k K).FG`)
and separable. There is a `k`-subalgebra `B` of `K` such that `k → B` is smooth and `K` is the
fraction field of `B` (`IsFractionRing B K`: every element of `K` is `b/b'` with `b, b' ∈ B`,
`b' ≠ 0`).
Source: Stacks Project, Algebra, Lemma Tag 037X (lemma-localization-smooth-separable),
implication “separable => localization of a smooth k-algebra”.
(blueprint: lem-weil-pbc-separable-extension-fraction-field-of-smooth-algebra). The proof first
chooses a
finite-type domain with fraction field `K`, applies smoothness at the generic point, and then
localizes at a nonzero element.
-/
theorem exists_smooth_subalgebra_fraction_field
    {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) (hsep : Algebra.IsSeparableExtension k K) :
    ∃ B : Subalgebra k K,
      Algebra.Smooth k B ∧ IsFractionRing B K := by
  classical
  obtain ⟨t, ht⟩ := hfg
  let A : Subalgebra k K := Algebra.adjoin k (↑t : Set K)
  have : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite t.finite_toSet
  have : IsFractionRing A K := by
    apply IsFractionRing.of_field
    intro z
    have hz : z ∈ IntermediateField.adjoin k (↑t : Set K) := by rw [ht]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  have hsm : Algebra.IsSmoothAtPrime k
      (⟨(⊥ : Ideal A), inferInstance⟩ : PrimeSpectrum A) :=
    Algebra.smoothAtPrime_bot_of_isSeparable_fractionRing k A K hsep
  obtain ⟨g, hg, hgs⟩ := hsm
  have hg0 : g ≠ 0 := by simpa using hg
  let f : A →ₐ[k] K := A.val
  have hunit : IsUnit (f g) := isUnit_iff_ne_zero.mpr
    (fun hz ↦ hg0 (Subtype.ext hz))
  let φ : Localization.Away g →ₐ[k] K :=
    IsLocalization.Away.liftAlgHom g hunit
  have hφ : Function.Injective φ := by
    change Function.Injective (IsLocalization.Away.lift g hunit)
    apply (IsLocalization.lift_injective_iff _).mpr
    intro x y
    constructor
    · intro h
      exact Subtype.ext_iff.mp
        (IsLocalization.injective (Localization.Away g)
          (powers_le_nonZeroDivisors_of_noZeroDivisors hg0) h)
    · intro h
      exact congrArg (algebraMap A (Localization.Away g)) (Subtype.ext h)
  let B : Subalgebra k K := φ.range
  let e : Localization.Away g ≃ₐ[k] B :=
    AlgEquiv.ofBijective φ.rangeRestrict
      ⟨fun x y h ↦ hφ (congrArg Subtype.val h), φ.rangeRestrict_surjective⟩
  have : Algebra.Smooth k (Localization.Away g) := hgs
  refine ⟨B, Algebra.Smooth.of_equiv e, ?_⟩
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective A z
  have haB : (a : K) ∈ B := by
    refine ⟨algebraMap A (Localization.Away g) a, ?_⟩
    exact IsLocalization.Away.lift_eq g hunit a
  have hbB : (b : K) ∈ B := by
    refine ⟨algebraMap A (Localization.Away g) b, ?_⟩
    exact IsLocalization.Away.lift_eq g hunit b
  exact ⟨⟨a, haB⟩, ⟨b, hbB⟩, hz.symm⟩

end FieldTheory

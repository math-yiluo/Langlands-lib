/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Basic

/-! The localization family associated to a smooth fraction-field subalgebra.
Source: Stacks Project, Algebra, Tag 07BV (lemma-colimit-syntomic), separable case.
(blueprint: new-smooth-fraction-field-localizations) -/

@[expose] public section

universe u v

namespace FieldTheory

/-- A smooth subalgebra whose fraction field is `L` gives a directed
family of smooth finitely generated subalgebras covering `L`. For each nonzero `f` in `B`,
use the principal localization `B[1/f]`; transport smoothness and finite generation across
its canonical embedding into `L`. Multiplication of denominators supplies directedness,
and the fraction-ring property supplies the covering statement.
Source: Stacks Project, Algebra, Tag 07BV (lemma-colimit-syntomic), separable case.
(blueprint: new-smooth-fraction-field-localizations) -/
theorem exists_smooth_fg_localization_family
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (B : Subalgebra K L) (hBsm : Algebra.Smooth K B)
    (hfrac : IsFractionRing B L) :
    ∃ (ι : Type v) (A : ι → Subalgebra K L),
      Nonempty ι ∧
        (∀ i, Algebra.Smooth K (A i)) ∧
        (∀ i, (A i).FG) ∧
        Directed (· ≤ ·) A ∧
        ∀ x : L, ∃ i, x ∈ A i := by
  classical
  let ι := {f : B // f ≠ 0}
  have hne (f : ι) : (f.1 : L) ≠ 0 := fun h ↦ f.2 (Subtype.ext h)
  let φ (f : ι) : Localization.Away f.1 →ₐ[K] L :=
    IsLocalization.Away.liftAlgHom (f := B.val) f.1
      (isUnit_iff_ne_zero.mpr (hne f))
  let A (f : ι) : Subalgebra K L := (φ f).range
  have hφ (f : ι) (a : B) : φ f (algebraMap B (Localization.Away f.1) a) = a :=
    IsLocalization.Away.lift_eq f.1 (isUnit_iff_ne_zero.mpr (hne f)) a
  have hinv (f : ι) : (f.1 : L) * φ f (IsLocalization.Away.invSelf f.1) = 1 := by
    have h := congrArg (φ f) (IsLocalization.Away.mul_invSelf
      (S := Localization.Away f.1) f.1)
    simpa only [map_mul, map_one, hφ] using h
  have hmem (f : ι) (z : L) : z ∈ A f ↔ ∃ n : ℕ, ∃ a : B,
      z * (f.1 : L) ^ n = a := by
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f.1 y
      refine ⟨n, a, ?_⟩
      change φ f y * (f.1 : L) ^ n = a
      have h := congrArg (φ f) ha
      simpa only [map_mul, map_pow, hφ] using h
    · rintro ⟨n, a, ha⟩
      refine ⟨algebraMap B (Localization.Away f.1) a *
        IsLocalization.Away.invSelf f.1 ^ n, ?_⟩
      change φ f (algebraMap B (Localization.Away f.1) a *
        IsLocalization.Away.invSelf f.1 ^ n) = z
      apply mul_right_cancel₀ (pow_ne_zero n (hne f))
      rw [ha, map_mul, map_pow, hφ]
      rw [mul_assoc, ← mul_pow, mul_comm (φ f _), hinv, one_pow, mul_one]
  have hsm (f : ι) : Algebra.Smooth K (A f) := by
    have : Algebra.Smooth B (Localization.Away f.1) :=
      Algebra.Smooth.of_isLocalization_Away f.1
    have : Algebra.Smooth K (Localization.Away f.1) :=
      Algebra.Smooth.comp K B (Localization.Away f.1)
    have hi : Function.Injective (φ f) := by
      change Function.Injective (IsLocalization.Away.lift f.1
        (isUnit_iff_ne_zero.mpr (hne f)))
      apply (IsLocalization.lift_injective_iff _).mpr
      intro x y
      constructor
      · intro h
        exact Subtype.ext_iff.mp
          (IsLocalization.injective (Localization.Away f.1)
            (powers_le_nonZeroDivisors_of_noZeroDivisors f.2) h)
      · intro h
        exact congrArg (algebraMap B (Localization.Away f.1)) (Subtype.ext h)
    exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective (φ f).rangeRestrict
      ⟨fun x y h ↦ hi (congrArg Subtype.val h), (φ f).rangeRestrict_surjective⟩)
  refine ⟨ι, A, ⟨⟨1, one_ne_zero⟩⟩, hsm, ?_, ?_, ?_⟩
  · intro f
    have : Algebra.Smooth K (A f) := hsm f
    exact (A f).fg_iff_finiteType.mpr inferInstance
  · intro f g
    let fg : ι := ⟨f.1 * g.1, mul_ne_zero f.2 g.2⟩
    refine ⟨fg, ?_, ?_⟩
    · intro z hz
      obtain ⟨n, a, ha⟩ := (hmem f z).mp hz
      apply (hmem fg z).mpr
      refine ⟨n, a * g.1 ^ n, ?_⟩
      change z * ((f.1 : L) * (g.1 : L)) ^ n = (a : L) * (g.1 : L) ^ n
      rw [mul_pow, ← mul_assoc, ha]
    · intro z hz
      obtain ⟨n, a, ha⟩ := (hmem g z).mp hz
      apply (hmem fg z).mpr
      refine ⟨n, a * f.1 ^ n, ?_⟩
      change z * ((f.1 : L) * (g.1 : L)) ^ n = (a : L) * (f.1 : L) ^ n
      rw [mul_comm (f.1 : L), mul_pow, ← mul_assoc, ha]
  · intro z
    obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective B z
    have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    refine ⟨⟨b, hb⟩, (hmem ⟨b, hb⟩ z).mpr ⟨1, a, ?_⟩⟩
    have hbL : (b : L) ≠ 0 := fun h ↦ hb (Subtype.ext h)
    rw [pow_one, ← hz]
    change (a : L) / (b : L) * (b : L) = a
    exact div_mul_cancel₀ _ hbL

end FieldTheory

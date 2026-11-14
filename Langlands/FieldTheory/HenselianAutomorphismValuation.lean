import Langlands.FieldTheory.HenselianFiniteGaloisInvariant
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Norm.Transitivity

/-! # Automorphism invariance of Henselian discrete valuations -/

noncomputable section

open scoped NNReal
open Polynomial IsLocalRing

namespace Langlands.FieldTheory

section Automorphism

variable {K : Type*} [Field K]

/-- A nonzero element with `n`-th roots for arbitrarily large exponents `n`.
This property is defined from the field structure alone. -/
def HasUnboundedRoots (x : K) : Prop :=
  x ≠ 0 ∧ ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ y : K, y ^ n = x

/-- Ring automorphisms preserve the property of having unboundedly many roots. -/
theorem hasUnboundedRoots_map (σ : K ≃+* K) (x : K) :
    HasUnboundedRoots (σ x) ↔ HasUnboundedRoots x := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨fun hx => h0 (by rw [hx, map_zero]), fun N => ?_⟩
    obtain ⟨n, hn, y, hy⟩ := h N
    exact ⟨n, hn, σ.symm y, by rw [← map_pow, hy, RingEquiv.symm_apply_apply]⟩
  · rintro ⟨h0, h⟩
    refine ⟨(map_ne_zero σ).mpr h0, fun N => ?_⟩
    obtain ⟨n, hn, y, hy⟩ := h N
    exact ⟨n, hn, σ y, by rw [← map_pow, hy]⟩

variable (v : Valuation K (WithZero (Multiplicative ℤ)))

/-- An element with unboundedly many roots has value one for every integer-valued
valuation: an `n`-th root forces `n` to divide the integer order. -/
theorem val_eq_one_of_hasUnboundedRoots {x : K} (hx : HasUnboundedRoots x) : v x = 1 := by
  obtain ⟨h0, h⟩ := hx
  obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp ((Valuation.ne_zero_iff v).mpr h0)
  by_contra hne
  have hm0 : Multiplicative.toAdd m ≠ 0 := by
    intro hm0
    apply hne
    rw [← hm, show m = 1 from hm0, WithZero.coe_one]
  obtain ⟨n, hn, y, hy⟩ := h ((Multiplicative.toAdd m).natAbs + 1)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply h0
    rw [← hy, zero_pow (by omega)]
  obtain ⟨j, hj⟩ := WithZero.ne_zero_iff_exists.mp ((Valuation.ne_zero_iff v).mpr hy0)
  have hjm : j ^ n = m := by
    apply WithZero.coe_injective
    rw [WithZero.coe_pow, hj, hm, ← map_pow, hy]
  have hdvd : (n : ℤ) ∣ Multiplicative.toAdd m :=
    ⟨Multiplicative.toAdd j, by rw [← hjm, toAdd_pow, nsmul_eq_mul]⟩
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hm0) (Int.natAbs_dvd_natAbs.mpr hdvd)
  simp only [Int.natAbs_natCast] at hle
  omega

/-- Over a Henselian valuation ring with algebraically closed residue field, every unit
has an `n`-th root whenever `n` is invertible in the residue field. -/
theorem hasUnboundedRoots_of_val_eq_one [HenselianLocalRing v.valuationSubring]
    [IsAlgClosed (ResidueField v.valuationSubring)] {x : K} (hx : v x = 1) :
    HasUnboundedRoots x := by
  have h0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  refine ⟨h0, fun N => ?_⟩
  set O := v.valuationSubring
  obtain ⟨n, hn, hn0⟩ : ∃ n : ℕ, N ≤ n ∧ (n : ResidueField O) ≠ 0 := by
    rcases Nat.eq_zero_or_pos (ringChar (ResidueField O)) with hp | hp
    · refine ⟨N + 1, by omega, fun h => ?_⟩
      rw [ringChar.spec, hp, zero_dvd_iff] at h
      omega
    · refine ⟨N * ringChar (ResidueField O) + 1, by nlinarith, fun h => ?_⟩
      rw [ringChar.spec, Nat.dvd_add_right (Dvd.intro_left _ rfl), Nat.dvd_one] at h
      exact CharP.ringChar_ne_one h
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by rw [h, Nat.cast_zero]) hn0
    · exact h
  let u : O := ⟨x, (v.mem_valuationSubring_iff x).mpr hx.le⟩
  have hxinv : x⁻¹ ∈ O := by
    rw [v.mem_valuationSubring_iff, map_inv₀, hx, inv_one]
  have hu : IsUnit u :=
    IsUnit.of_mul_eq_one (⟨x⁻¹, hxinv⟩ : O) (Subtype.ext (mul_inv_cancel₀ h0))
  have hu0 : residue O u ≠ 0 := (residue_ne_zero_iff_isUnit u).mpr hu
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (residue O u) hnpos
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hnpos.ne'] at hz
    exact hu0 hz.symm
  obtain ⟨a₀, ha₀⟩ := residue_surjective z
  let f : O[X] := X ^ n - C u
  have hf : f.Monic := monic_X_pow_sub_C u hnpos.ne'
  have heval : f.eval a₀ ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]
    simp only [f, eval_sub, eval_pow, eval_X, eval_C, map_sub, map_pow, ha₀, hz, sub_self]
  have hder : IsUnit (f.derivative.eval a₀) := by
    rw [← residue_ne_zero_iff_isUnit]
    simp only [f, derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul,
      eval_natCast, eval_pow, eval_X, map_mul, map_pow, map_natCast, ha₀]
    exact mul_ne_zero (by exact_mod_cast hn0) (pow_ne_zero _ hz0)
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian f hf a₀ heval hder
  refine ⟨n, hn, (a : K), ?_⟩
  have hau : a ^ n = u := by
    simpa only [f, IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using ha
  exact congrArg Subtype.val hau

/-- On a Henselian integer-valued field with algebraically closed residue field, the
units of the valuation ring are exactly the elements with unboundedly many roots. -/
theorem val_eq_one_iff_hasUnboundedRoots [HenselianLocalRing v.valuationSubring]
    [IsAlgClosed (ResidueField v.valuationSubring)] (x : K) :
    v x = 1 ↔ HasUnboundedRoots x :=
  ⟨hasUnboundedRoots_of_val_eq_one v, val_eq_one_of_hasUnboundedRoots v⟩

/-- An element is integral exactly when it or its translate by one is a unit. -/
theorem val_le_one_iff_eq_one_or_add_eq_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation K Γ₀) (x : K) : w x ≤ 1 ↔ w x = 1 ∨ w (1 + x) = 1 := by
  constructor
  · intro h
    rcases h.lt_or_eq with h | h
    · exact Or.inr (w.map_one_add_of_lt h)
    · exact Or.inl h
  · rintro (h | h)
    · exact h.le
    · by_contra hx
      push Not at hx
      have h1 : w 1 < w x := by rwa [map_one]
      rw [w.map_add_eq_of_lt_right h1] at h
      exact hx.ne' h

/-- Every ring automorphism of a Henselian integer-valued field with algebraically closed
residue field preserves the valuation up to equivalence. -/
theorem isEquiv_comap_ringEquiv [HenselianLocalRing v.valuationSubring]
    [IsAlgClosed (ResidueField v.valuationSubring)] (σ : K ≃+* K) :
    (v.comap (σ : K →+* K)).IsEquiv v := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  have h1 : 1 + σ x = σ (1 + x) := by rw [map_add, map_one]
  simp only [Valuation.comap_apply, RingEquiv.coe_toRingHom]
  rw [val_le_one_iff_eq_one_or_add_eq_one v (σ x), val_le_one_iff_eq_one_or_add_eq_one v x,
    h1, val_eq_one_iff_hasUnboundedRoots, val_eq_one_iff_hasUnboundedRoots,
    val_eq_one_iff_hasUnboundedRoots, val_eq_one_iff_hasUnboundedRoots,
    hasUnboundedRoots_map, hasUnboundedRoots_map]

end Automorphism

section Prolongation

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]

/-- A Galois-invariant real valuation sees integrality through the norm. -/
theorem realValuation_le_one_iff_norm (w : Valuation Ω ℝ≥0)
    (hw : ∀ (σ : Gal(Ω/K)) (x : Ω), w (σ x) = w x) (a : Ω) :
    w a ≤ 1 ↔ w.comap (algebraMap K Ω) (Algebra.norm K a) ≤ 1 := by
  classical
  rw [Valuation.comap_apply, Algebra.norm_eq_prod_automorphisms, map_prod]
  simp_rw [hw]
  rw [Finset.prod_const, Finset.card_univ,
    pow_le_one_iff_of_nonneg zero_le Fintype.card_ne_zero]

/-- Two real valuations on a finite Galois extension of a field which is Henselian for a
nontrivial valuation are equivalent when their restrictions are equivalent. -/
theorem realValuation_isEquiv_of_comap_isEquiv (w₁ w₂ : Valuation Ω ℝ≥0)
    (hnt : (w₁.comap (algebraMap K Ω)).IsNontrivial)
    [hH : HenselianLocalRing (w₁.comap (algebraMap K Ω)).valuationSubring]
    (he : (w₁.comap (algebraMap K Ω)).IsEquiv (w₂.comap (algebraMap K Ω))) :
    w₁.IsEquiv w₂ := by
  have hnt₂ : (w₂.comap (algebraMap K Ω)).IsNontrivial := Valuation.isNontrivial_of_isEquiv he hnt
  have hH₂ : HenselianLocalRing (w₂.comap (algebraMap K Ω)).valuationSubring := by
    rw [← (Valuation.isEquiv_iff_valuationSubring _ _).mp he]
    exact hH
  have hinv₁ := realValuation_invariant_of_finiteGalois _ hnt w₁ rfl
  have hinv₂ := realValuation_invariant_of_finiteGalois _ hnt₂ w₂ rfl
  rw [Valuation.isEquiv_iff_val_le_one]
  intro a
  rw [realValuation_le_one_iff_norm w₁ hinv₁, realValuation_le_one_iff_norm w₂ hinv₂]
  exact Valuation.isEquiv_iff_val_le_one.mp he

end Prolongation

end Langlands.FieldTheory

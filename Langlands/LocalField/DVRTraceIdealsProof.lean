import Langlands.LocalField.DVRTraceIdealsStatement
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

namespace Langlands.LocalField

universe uA uB uK uL

namespace DVRTraceIdealsAux

open IsLocalRing nonZeroDivisors

variable {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Field K] [Field L] [Algebra A B] [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]
  [Module.Finite A B] [Module.IsTorsionFree A B]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] in
lemma trace_inv_mul (a : A) (z : L) :
    Algebra.trace K L ((algebraMap A L a)⁻¹ * z) =
      (algebraMap A K a)⁻¹ * Algebra.trace K L z := by
  rw [IsScalarTower.algebraMap_apply A K L, ← map_inv₀, ← Algebra.smul_def,
    map_smul, smul_eq_mul]

omit [IsFractionRing B L] [Algebra.IsSeparable K L] in
lemma trace_div_mem_range_iff (a : A) (ha : a ≠ 0) (x : B) :
    (algebraMap A K a)⁻¹ * Algebra.trace K L (algebraMap B L x) ∈
      (algebraMap A K).range ↔ Algebra.intTrace A B x ∈ Ideal.span {a} := by
  have haK : algebraMap A K a ≠ 0 := by simpa using (IsFractionRing.injective A K).ne ha
  rw [← Algebra.algebraMap_intTrace (A := A), Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, (IsFractionRing.injective A K) ?_⟩
    rw [map_mul, hz, ← mul_assoc, mul_inv_cancel₀ haK, one_mul]
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz, map_mul, inv_mul_cancel_left₀ haK]⟩

lemma scaled_mem_dual_iff (J : Ideal B) (a : A) (ha : a ≠ 0) :
    FractionalIdeal.spanSingleton B⁰ (algebraMap A L a)⁻¹ *
      (J : FractionalIdeal B⁰ L) ≤ FractionalIdeal.dual A K 1 ↔
    ∀ x ∈ J, Algebra.intTrace A B x ∈ Ideal.span {a} := by
  rw [FractionalIdeal.spanSingleton_mul_le_iff]
  constructor
  · intro h x hx
    have hm := (FractionalIdeal.mem_dual (A := A) (K := K) one_ne_zero).mp
      (h (algebraMap B L x) ⟨x, hx, rfl⟩)
    have hh := hm 1 (by simp)
    rw [Algebra.traceForm_apply, mul_one] at hh
    apply (trace_div_mem_range_iff (K := K) (L := L) a ha x).mp
    simpa only [trace_inv_mul (K := K)] using hh
  · intro h z hz
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hz
    rw [FractionalIdeal.mem_dual (A := A) (K := K) one_ne_zero]
    intro b hb
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp hb
    subst hb
    have hh := (trace_div_mem_range_iff (K := K) (L := L) a ha (x * b)).mpr
      (h (x * b) (J.mul_mem_right b hx))
    rw [Algebra.traceForm_apply, mul_assoc, ← map_mul]
    simpa only [trace_inv_mul (K := K)] using hh

noncomputable def traceIdeal (J : Ideal B) : Ideal A :=
  (J.restrictScalars A).map (Algebra.intTrace A B)

include K L in
lemma traceIdeal_le_span_iff (J : Ideal B) (a : A) (ha : a ≠ 0) :
    traceIdeal J ≤ Ideal.span {a} ↔
      differentIdeal A B * J ≤ Ideal.span {algebraMap A B a} := by
  have haK : algebraMap A K a ≠ 0 := by
    simpa using (IsFractionRing.injective A K).ne ha
  have haL : algebraMap A L a ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact (map_ne_zero (algebraMap K L)).mpr haK
  have hS : (FractionalIdeal.spanSingleton B⁰ (algebraMap A L a) :
      FractionalIdeal B⁰ L) ≠ 0 := by
    simpa only [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff] using haL
  have hC := FractionalIdeal.dual_ne_zero A K
    (one_ne_zero : (1 : FractionalIdeal B⁰ L) ≠ 0)
  change (J.restrictScalars A).map (Algebra.intTrace A B) ≤ _ ↔ _
  rw [Submodule.map_le_iff_le_comap]
  change (∀ x ∈ J, Algebra.intTrace A B x ∈ Ideal.span {a}) ↔ _
  rw [← scaled_mem_dual_iff (K := K) (L := L) J a ha,
    ← FractionalIdeal.coeIdeal_le_coeIdeal L, FractionalIdeal.coeIdeal_mul,
    coeIdeal_differentIdeal A K L B, FractionalIdeal.coeIdeal_span_singleton,
    ← IsScalarTower.algebraMap_apply A B L,
    ← FractionalIdeal.spanSingleton_inv,
    inv_mul_le_iff₀ (pos_iff_ne_zero.mpr hS),
    inv_mul_le_iff₀ (pos_iff_ne_zero.mpr hC), mul_comm]

include K L in
lemma traceIdeal_le_pow_iff (e d n r : ℕ)
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e)
    (hd : differentIdeal A B = maximalIdeal B ^ d) :
    traceIdeal (maximalIdeal B ^ n) ≤ maximalIdeal A ^ r ↔ e * r ≤ d + n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hpow : maximalIdeal A ^ r = Ideal.span {π ^ r} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hm : Ideal.span {algebraMap A B (π ^ r)} = maximalIdeal B ^ (e * r) := by
    calc
      Ideal.span {algebraMap A B (π ^ r)} =
          Ideal.map (algebraMap A B) (maximalIdeal A ^ r) := by
        rw [hpow, Ideal.map_span, Set.image_singleton]
      _ = maximalIdeal B ^ (e * r) := by rw [Ideal.map_pow, hmap, ← pow_mul]
  rw [hpow, traceIdeal_le_span_iff (K := K) (L := L) _ _ (pow_ne_zero _ hπ.ne_zero),
    hd, hm, ← pow_add]
  exact (Ideal.pow_right_strictAnti (maximalIdeal B)
    (IsDiscreteValuationRing.not_a_field B) (Ideal.IsMaximal.ne_top inferInstance)).le_iff_ge

include K L in
lemma traceIdeal_eq_pow (e d n : ℕ) (he : 0 < e)
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e)
    (hd : differentIdeal A B = maximalIdeal B ^ d) :
    traceIdeal (maximalIdeal B ^ n) = maximalIdeal A ^ ((d + n) / e) := by
  have hcrit := traceIdeal_le_pow_iff (A := A) (B := B) (K := K) (L := L) e d n
  have hT : traceIdeal (A := A) (maximalIdeal B ^ n) ≠ ⊥ := by
    intro hT
    have hh := (hcrit (d + n + 1) hmap hd).mp (by rw [hT]; exact bot_le)
    have hm : d + n + 1 ≤ e * (d + n + 1) := Nat.le_mul_of_pos_left _ he
    omega
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hT hπ
  have hs' : traceIdeal (maximalIdeal B ^ n) = maximalIdeal A ^ s := by
    rw [hs, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hanti := Ideal.pow_right_strictAnti (maximalIdeal A)
    (IsDiscreteValuationRing.not_a_field A) (Ideal.IsMaximal.ne_top inferInstance)
  have heq : s = (d + n) / e := by
    apply Nat.le_antisymm
    · apply (Nat.le_div_iff_mul_le he).mpr
      simpa only [Nat.mul_comm] using (hcrit s hmap hd).mp (by rw [hs'])
    · have hh := (hcrit ((d + n) / e) hmap hd).mpr
        (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self (d + n) e)
      rw [hs'] at hh
      exact hanti.le_iff_ge.mp hh
  rw [hs', heq]

end DVRTraceIdealsAux

/-- The exact trace image of every nonnegative ideal power, using the supplied
field trace and the actual different ideal. -/
theorem dvrTraceIdeals : DVRTraceIdeals.{uA, uB, uK, uL} := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have := isTorsionFree_of_isFractionRing_tower A B K L
  intro e d he hmap hd n
  dsimp only
  intro y
  have hT := DVRTraceIdealsAux.traceIdeal_eq_pow (K := K) (L := L) e d n he hmap hd
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨Algebra.intTrace A B x, ?_, ?_⟩
    · rw [← hT]
      exact ⟨x, hx, rfl⟩
    · rw [Algebra.algebraMap_intTrace (L := L)]
      exact hxy
  · rintro ⟨a, ha, hay⟩
    rw [← hT] at ha
    obtain ⟨x, hx, hxa⟩ := ha
    refine ⟨x, hx, ?_⟩
    rw [← Algebra.algebraMap_intTrace (A := A), hxa, hay]

end Langlands.LocalField

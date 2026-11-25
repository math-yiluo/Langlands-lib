/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

/-!
# Galois subextensions of prime degree and degrees of Galois extensions

* `IsGalois.exists_isGalois_finrank_eq_prime_le_of_finrank_eq_prime_pow`: in a finite Galois
  extension `E/K` of degree `p ^ k`, every intermediate field `M ≠ K` contains an intermediate
  field `M'` which is Galois of degree `p` over `K` (`p`-group reduction).
* `IntermediateField.exists_isGalois_finrank_eq_prime_le`: the same inside an algebraically closed
  field `Ω`, assuming every finite Galois subextension of `Ω/L` has `p`-power degree.
* `IsGalois.exists_not_pow_eq_of_prime_dvd_finrank`: if `K` contains a primitive `ℓ`-th root of
  unity and `ℓ` divides the degree of a finite Galois extension `E/K`, some intermediate field of
  `E/K` contains an element that is not an `ℓ`-th power in it (Sylow + Kummer theory).
* `IntermediateField.mem_of_prime_dvd_finrank`: consequently, if every finite subextension of
  `Ω/L` is `ℓ`-divisible and `L` contains the `ℓ`-th roots of unity for all primes `ℓ ∉ S`, the
  prime factors of the degrees of finite Galois subextensions of `Ω/L` lie in `S`.
-/

@[expose] public section

open Module Polynomial IntermediateField

namespace IsGalois

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- **`p`-group reduction.** In a finite Galois extension `E/K` of degree `p ^ k`, every
intermediate field `M ≠ ⊥` contains an intermediate field which is Galois of degree `p`
over `K`. -/
theorem exists_isGalois_finrank_eq_prime_le_of_finrank_eq_prime_pow
    [FiniteDimensional K E] [IsGalois K E] {p k : ℕ} [hp : Fact p.Prime]
    (hE : finrank K E = p ^ k) (M : IntermediateField K E) (hM : M ≠ ⊥) :
    ∃ M' ≤ M, IsGalois K M' ∧ finrank K M' = p := by
  have hG : Nat.card Gal(E/K) = p ^ k := by rw [IsGalois.card_aut_eq_finrank, hE]
  have hH : Nat.card M.fixingSubgroup ∣ p ^ k := hG ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨n, hnk, hn⟩ := (Nat.dvd_prime_pow hp.out).1 hH
  have hnk' : n < k := by
    refine lt_of_le_of_ne hnk ?_
    rintro rfl
    apply hM
    have htop : M.fixingSubgroup = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hn, hG])
    rw [← fixedField_fixingSubgroup M, htop, ← fixingSubgroup_bot, fixedField_fixingSubgroup]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨H, hHcard, hMH⟩ := Sylow.exists_subgroup_card_pow_prime_le p
    (hG ▸ pow_dvd_pow p j.le_succ) M.fixingSubgroup hn (by omega)
  have hindex : H.index = p := by
    have h := H.card_mul_index
    rw [hHcard, hG, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos j) h
  have : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by
    rw [hindex, hG, Nat.Prime.pow_minFac hp.out (Nat.succ_ne_zero j)])
  refine ⟨fixedField H, ?_, inferInstance, ?_⟩
  · rw [← fixedField_fixingSubgroup M]
    exact fixedField_le hMH
  · have h := finrank_mul_finrank K (fixedField H) E
    rw [finrank_fixedField_eq_card, hHcard, hE, pow_succ, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos j) h

/-- **Sylow + Kummer.** Let `E/K` be a finite Galois extension whose degree is divisible by a
prime `ℓ`, and assume that `K` contains a primitive `ℓ`-th root of unity. Then some intermediate
field of `E/K` contains an element which is not an `ℓ`-th power in it. -/
theorem exists_not_pow_eq_of_prime_dvd_finrank [FiniteDimensional K E] [IsGalois K E]
    {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hζ : (primitiveRoots ℓ K).Nonempty)
    (hdvd : ℓ ∣ finrank K E) :
    ∃ F : IntermediateField K E, ∃ x : F, ∀ y : F, y ^ ℓ ≠ x := by
  obtain ⟨P⟩ : Nonempty (Sylow ℓ Gal(E/K)) := inferInstance
  set F := fixedField (P : Subgroup Gal(E/K))
  have hpos : 0 < (finrank K E).factorization ℓ :=
    hℓ.out.factorization_pos_of_dvd finrank_pos.ne' hdvd
  have hcard : finrank F E = ℓ ^ (finrank K E).factorization ℓ := by
    rw [finrank_fixedField_eq_card, Sylow.card_eq_multiplicity, IsGalois.card_aut_eq_finrank]
  have hne : (⊤ : IntermediateField F E) ≠ ⊥ := by
    intro h
    rw [eq_comm, bot_eq_top_iff_finrank_eq_one, hcard] at h
    exact (Nat.one_lt_pow hpos.ne' hℓ.out.one_lt).ne' h
  obtain ⟨F₁, -, hGal, hF₁⟩ :=
    exists_isGalois_finrank_eq_prime_le_of_finrank_eq_prime_pow hcard ⊤ hne
  obtain ⟨ζ, hζ⟩ := hζ
  rw [mem_primitiveRoots hℓ.out.pos] at hζ
  have hζF := hζ.map_of_injective (algebraMap K F).injective
  have : FiniteDimensional F F₁ := Module.finite_of_finrank_eq_succ (n := ℓ - 1) (by
    rw [hF₁]
    exact (Nat.succ_pred_eq_of_pos hℓ.out.pos).symm)
  have : IsCyclic Gal(F₁/F) := isCyclic_of_prime_card (p := ℓ) (by
    rw [IsGalois.card_aut_eq_finrank, hF₁])
  obtain ⟨θ, ⟨c, hc⟩, hθ⟩ := exists_root_adjoin_eq_top_of_isCyclic F F₁
    ⟨_, (mem_primitiveRoots finrank_pos).2 (hF₁ ▸ hζF)⟩
  rw [hF₁] at hc
  refine ⟨F, c, fun y hy => ?_⟩
  have hθF : θ ∉ Set.range (algebraMap F F₁) := by
    rintro ⟨a, rfl⟩
    rw [adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ a),
      bot_eq_top_iff_finrank_eq_one, hF₁] at hθ
    exact hℓ.out.one_lt.ne' hθ
  apply hθF
  have hζF₁ := hζF.map_of_injective (algebraMap F F₁).injective
  by_cases hy0 : y = 0
  · rw [hy0, zero_pow hℓ.out.ne_zero] at hy
    rw [← hy, map_zero, eq_comm, pow_eq_zero_iff hℓ.out.ne_zero] at hc
    exact ⟨0, by rw [map_zero, hc]⟩
  have hy' : algebraMap F F₁ y ≠ 0 := by simpa using hy0
  obtain ⟨i, -, hi⟩ := hζF₁.eq_pow_of_pow_eq_one (ξ := θ / algebraMap F F₁ y) (by
    rw [div_pow, ← map_pow, hy, hc, div_self]
    rw [← hc, ← hy, map_pow]
    exact pow_ne_zero _ hy')
  refine ⟨y * algebraMap K F ζ ^ i, ?_⟩
  rw [map_mul, map_pow, hi, mul_div_cancel₀ _ hy']

end IsGalois

namespace IntermediateField

variable {L Ω : Type*} [Field L] [Field Ω] [Algebra L Ω]

/-- **`p`-group reduction in an algebraically closed field.** If every finite Galois
subextension of `Ω/L` has `p`-power degree, then every finite separable subextension `M ≠ L`
of `Ω/L` contains a subextension which is Galois of degree `p` over `L`. -/
theorem exists_isGalois_finrank_eq_prime_le [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime]
    (h : ∀ N : IntermediateField L Ω, FiniteDimensional L N → IsGalois L N →
      ∃ k, finrank L N = p ^ k)
    (M : IntermediateField L Ω) [FiniteDimensional L M] [Algebra.IsSeparable L M]
    (hM : M ≠ ⊥) : ∃ M' ≤ M, IsGalois L M' ∧ finrank L M' = p := by
  set N := normalClosure L M Ω
  have : Normal L N :=
    (Algebra.IsAlgebraic.isNormalClosure_normalClosure fun _ => IsAlgClosed.splits _).normal
  have : Algebra.IsSeparable L N := by
    rw [← le_separableClosure_iff, normalClosure_le_iff]
    rintro f _ ⟨x, rfl⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, mem_separableClosure_iff, IsSeparable,
      minpoly.algHom_eq f f.injective]
    exact Algebra.IsSeparable.isSeparable L x
  have : IsGalois L N := ⟨⟩
  obtain ⟨k, hk⟩ := h N inferInstance inferInstance
  have hMN : M ≤ N := le_normalClosure M
  obtain ⟨M'', hM'', hGal, hfin⟩ :=
    IsGalois.exists_isGalois_finrank_eq_prime_le_of_finrank_eq_prime_pow hk (restrict hMN)
      (by
        intro h
        apply hM
        rw [← lift_restrict hMN, h, lift_bot])
  refine ⟨lift M'', ?_, IsGalois.of_algEquiv (liftAlgEquiv M''), ?_⟩
  · rw [← lift_restrict hMN]
    exact map_mono _ hM''
  · rw [← (liftAlgEquiv M'').toLinearEquiv.finrank_eq, hfin]

/-- **No `ℓ`-extensions implies restricted degrees.** Let `S` be a set of natural numbers.
Assume that for every prime `ℓ ∉ S`, the field `L` contains a primitive `ℓ`-th root of unity and
every element of every finite subextension `F` of `Ω/L` is an `ℓ`-th power in `F`. Then every
prime factor of the degree of a finite Galois subextension of `Ω/L` lies in `S`. -/
theorem mem_of_prime_dvd_finrank (S : Set ℕ)
    (hζ : ∀ ℓ, ℓ.Prime → ℓ ∉ S → (primitiveRoots ℓ L).Nonempty)
    (hpow : ∀ ℓ, ℓ.Prime → ℓ ∉ S → ∀ F : IntermediateField L Ω, FiniteDimensional L F →
      ∀ x ∈ F, ∃ y ∈ F, y ^ ℓ = x)
    (N : IntermediateField L Ω) [FiniteDimensional L N] [IsGalois L N]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdvd : ℓ ∣ finrank L N) : ℓ ∈ S := by
  by_contra hS
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨F, x, hx⟩ := IsGalois.exists_not_pow_eq_of_prime_dvd_finrank (hζ ℓ hℓ hS) hdvd
  have : FiniteDimensional L (lift F) := (liftAlgEquiv F).toLinearEquiv.finiteDimensional
  obtain ⟨y, hy, hyx⟩ := hpow ℓ hℓ hS (lift F) inferInstance _ (liftAlgEquiv F x).2
  apply hx ((liftAlgEquiv F).symm ⟨y, hy⟩)
  rw [← map_pow, AlgEquiv.symm_apply_eq]
  exact Subtype.ext hyx

/-- With `S = {p}`: the degree of every finite Galois subextension of `Ω/L` is a power of `p`. -/
theorem exists_finrank_eq_pow_of_forall_pow_eq {p : ℕ}
    (hζ : ∀ ℓ, ℓ.Prime → ℓ ≠ p → (primitiveRoots ℓ L).Nonempty)
    (hpow : ∀ ℓ, ℓ.Prime → ℓ ≠ p → ∀ F : IntermediateField L Ω, FiniteDimensional L F →
      ∀ x ∈ F, ∃ y ∈ F, y ^ ℓ = x)
    (N : IntermediateField L Ω) [FiniteDimensional L N] [IsGalois L N] :
    ∃ k, finrank L N = p ^ k :=
  ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd finrank_pos.ne' fun hℓ hdvd =>
    mem_of_prime_dvd_finrank {p} hζ hpow N hℓ hdvd⟩

/-- With `S = ∅`: every finite Galois subextension of `Ω/L` is trivial. -/
theorem finrank_eq_one_of_forall_pow_eq
    (hζ : ∀ ℓ, ℓ.Prime → (primitiveRoots ℓ L).Nonempty)
    (hpow : ∀ ℓ, ℓ.Prime → ∀ F : IntermediateField L Ω, FiniteDimensional L F →
      ∀ x ∈ F, ∃ y ∈ F, y ^ ℓ = x)
    (N : IntermediateField L Ω) [FiniteDimensional L N] [IsGalois L N] :
    finrank L N = 1 :=
  Nat.eq_one_iff_not_exists_prime_dvd.2 fun _ hℓ hdvd =>
    mem_of_prime_dvd_finrank ∅ (fun ℓ hℓ _ => hζ ℓ hℓ) (fun ℓ hℓ _ => hpow ℓ hℓ) N hℓ hdvd

end IntermediateField

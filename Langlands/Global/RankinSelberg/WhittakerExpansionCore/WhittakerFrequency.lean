import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerHeights
import Langlands.Global.RankinSelberg.EqualAnalyticLattice

/-! # Frequencies and sizes of algebraic integers

Two elementary ingredients of the decay estimate.

* Finitely many column directions detect the size of a rational row: the real frequencies
  `Tr(b ξ_a e_k)` along the directions `Pi.single a e_k` (with `e_k` the lattice basis of the
  mixed space) bound `‖ξ‖` from below, linearly.
* A nonzero algebraic integer `η` has mixed norm at least `1`, its inverse has mixed norm at most
  `‖η‖^(d-1)`, and the positive integer `|N(η)|` is a denominator of `η⁻¹` of size at most
  `‖η‖^d`, where `d = [F : ℚ]`. -/

noncomputable section
universe u
open NumberField
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F]

section Frequency

open scoped Classical

theorem colFrequency_single {r : ℕ} (b : F) (ξ : Fin (r + 1) → F) (a : Fin (r + 1))
    (u : mixedEmbedding.mixedSpace F) :
    colFrequency F b ξ (Pi.single a u) =
      mixedTrace F (mixedEmbedding F b * (mixedEmbedding F (ξ a) * u)) := by
  classical
  rw [colFrequency, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro c _ hc
    rw [Pi.single_eq_of_ne hc, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- **Frequencies detect sizes.** For `b ≠ 0` there is `K₀ ≥ 0` with
`‖ξ_a‖ ≤ K₀ Σ_k |Tr(b ξ_a e_k)|` for every rational row `ξ` and index `a`. -/
theorem exists_norm_le_sum_colFrequency {b : F} (hb : b ≠ 0) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (r : ℕ) (ξ : Fin (r + 1) → F) (a : Fin (r + 1)),
      ‖mixedEmbedding F (ξ a)‖ ≤
        K₀ * ∑ k, |colFrequency F b ξ (Pi.single a (mixedEmbedding.latticeBasis F k))| := by
  set Λ := (mixedTracePairing F).comp (LinearMap.mulLeft ℝ (mixedEmbedding F b)) with hΛ
  have hinj : Function.Injective Λ := by
    intro z z' h
    have h1 := mixedTracePairing_injective F h
    simp only [LinearMap.mulLeft_apply] at h1
    have hb' : mixedEmbedding F b⁻¹ * mixedEmbedding F b = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb, map_one]
    calc z = mixedEmbedding F b⁻¹ * (mixedEmbedding F b * z) := by
          rw [← mul_assoc, hb', one_mul]
      _ = mixedEmbedding F b⁻¹ * (mixedEmbedding F b * z') := by rw [h1]
      _ = z' := by rw [← mul_assoc, hb', one_mul]
  obtain ⟨K₀, hK₀, hK⟩ := EqualAnalytic.exists_norm_le_sum_of_injective Λ hinj
  refine ⟨K₀, hK₀, fun r ξ a => ?_⟩
  refine (hK (mixedEmbedding F (ξ a))).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [colFrequency_single]
  simp only [hΛ, LinearMap.comp_apply, LinearMap.mulLeft_apply, mixedTracePairing,
    LinearMap.pi_apply]
  congr 2
  ring

/-- `(Σ x_i)^K ≤ (card ι)^K Σ x_i^K` for nonnegative `x`. -/
theorem sum_pow_le_card_pow_mul_sum_pow {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (K : ℕ) :
    (∑ i, x i) ^ K ≤ (Fintype.card ι : ℝ) ^ K * ∑ i, x i ^ K := by
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
  have h1 : ∑ i, x i ≤ Fintype.card ι * x i₀ := by
    have := Finset.sum_le_sum fun i (hi : i ∈ Finset.univ) => hi₀ i hi
    simpa [Finset.sum_const, Finset.card_univ] using this
  have h2 : x i₀ ^ K ≤ ∑ i, x i ^ K :=
    Finset.single_le_sum (f := fun i => x i ^ K) (fun i _ => pow_nonneg (hx i) K)
      (Finset.mem_univ i₀)
  calc (∑ i, x i) ^ K ≤ (Fintype.card ι * x i₀) ^ K :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => hx i) h1 K
    _ = (Fintype.card ι : ℝ) ^ K * x i₀ ^ K := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (pow_nonneg (Nat.cast_nonneg _) K)

end Frequency

section Integers

open scoped Classical

theorem norm_mixedEmbedding_mul_le (x y : F) :
    ‖mixedEmbedding F (x * y)‖ ≤ ‖mixedEmbedding F x‖ * ‖mixedEmbedding F y‖ := by
  rw [norm_mixedEmbedding_le_iff]
  intro w
  rw [map_mul]
  exact mul_le_mul (le_norm_mixedEmbedding F x w) (le_norm_mixedEmbedding F y w)
    (apply_nonneg _ _) (norm_nonneg _)

theorem norm_mixedEmbedding_natCast (n : ℕ) : ‖mixedEmbedding F (n : F)‖ = n := by
  apply le_antisymm
  · rw [norm_mixedEmbedding_le_iff]
    intro w
    rw [← InfinitePlace.norm_embedding_eq w (n : F), map_natCast, Complex.norm_natCast]
  · have w : InfinitePlace F := Classical.arbitrary _
    have h := le_norm_mixedEmbedding F (n : F) w
    rwa [← InfinitePlace.norm_embedding_eq w (n : F), map_natCast, Complex.norm_natCast] at h

theorem norm_mixedEmbedding_div_natCast (x : F) (n : ℕ) :
    ‖mixedEmbedding F (x / n)‖ = ‖mixedEmbedding F x‖ / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply le_antisymm
  · rw [norm_mixedEmbedding_le_iff]
    intro w
    rw [map_div₀, ← InfinitePlace.norm_embedding_eq w (n : F), map_natCast,
      Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (le_norm_mixedEmbedding F x w) hn'.le
  · have h : ‖mixedEmbedding F x‖ ≤ ‖mixedEmbedding F (x / n)‖ * n := by
      have hx : x = x / n * n := by
        rw [div_mul_cancel₀]
        exact_mod_cast hn.ne'
      calc ‖mixedEmbedding F x‖ = ‖mixedEmbedding F (x / n * n)‖ := by rw [← hx]
        _ ≤ ‖mixedEmbedding F (x / n)‖ * ‖mixedEmbedding F (n : F)‖ :=
          norm_mixedEmbedding_mul_le F _ _
        _ = _ := by rw [norm_mixedEmbedding_natCast]
    rwa [div_le_iff₀ hn']

/-- A nonzero algebraic integer has mixed norm at least `1`. -/
theorem one_le_norm_mixedEmbedding {η : 𝓞 F} (hη : η ≠ 0) :
    1 ≤ ‖mixedEmbedding F (η : F)‖ := by
  by_contra h
  push Not at h
  have w₀ : InfinitePlace F := Classical.arbitrary _
  have h1 := InfinitePlace.one_le_of_lt_one (w := w₀) hη fun z _ =>
    (le_norm_mixedEmbedding F (η : F) z).trans_lt h
  exact absurd ((le_norm_mixedEmbedding F (η : F) w₀).trans_lt h) (not_lt.mpr h1)

theorem abs_norm_le_pow (x : F) {M : ℝ} (hx : ‖mixedEmbedding F x‖ ≤ M) :
    |(Algebra.norm ℚ x : ℝ)| ≤ M ^ Module.finrank ℚ F := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hx
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [← Rat.cast_abs, ← h, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun w _ => pow_nonneg (apply_nonneg _ _) _)
    fun w _ => pow_le_pow_left₀ (apply_nonneg _ _) ((le_norm_mixedEmbedding F x w).trans hx) _

theorem one_le_abs_norm {η : 𝓞 F} (hη : η ≠ 0) : (1 : ℝ) ≤ |(Algebra.norm ℚ (η : F) : ℝ)| := by
  rw [← Algebra.coe_norm_int, ← Rat.cast_abs, ← Int.cast_abs, Rat.cast_intCast]
  exact_mod_cast Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hη)

/-- **Inverse bound.** If `η ∈ 𝒪` is nonzero and `‖η‖ ≤ M`, then `‖η⁻¹‖ ≤ M^(d-1)`. -/
theorem norm_mixedEmbedding_inv_le {η : 𝓞 F} (hη : η ≠ 0) {M : ℝ}
    (hM : ‖mixedEmbedding F (η : F)‖ ≤ M) :
    ‖mixedEmbedding F (η : F)⁻¹‖ ≤ M ^ (Module.finrank ℚ F - 1) := by
  classical
  have hM1 : 1 ≤ M := (one_le_norm_mixedEmbedding F hη).trans hM
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hη' : (η : F) ≠ 0 := (Subalgebra.coe_eq_zero _).not.mpr hη
  rw [norm_mixedEmbedding_le_iff]
  intro w
  rw [map_inv₀]
  have hw0 : 0 < w (η : F) := InfinitePlace.pos_iff.mpr hη'
  have hle : ∀ w' : InfinitePlace F, w' (η : F) ≤ M := fun w' =>
    (le_norm_mixedEmbedding F _ w').trans hM
  set d := Module.finrank ℚ F
  have hsum : w.mult + ∑ w' ∈ Finset.univ.erase w, w'.mult = d := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ w), InfinitePlace.sum_mult_eq]
  have hm1 : 1 ≤ w.mult := InfinitePlace.mult_pos
  have hprod : (1 : ℝ) ≤ w (η : F) ^ w.mult *
      M ^ (∑ w' ∈ Finset.univ.erase w, w'.mult) := by
    have h := InfinitePlace.prod_eq_abs_norm (η : F)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)] at h
    calc (1 : ℝ) ≤ |(Algebra.norm ℚ (η : F) : ℝ)| := one_le_abs_norm F hη
      _ = _ := by rw [← Rat.cast_abs, ← h]
      _ ≤ _ := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun w' _ => pow_nonneg (apply_nonneg _ _) _)
          fun w' _ => pow_le_pow_left₀ (apply_nonneg _ _) (hle w') _)
          (pow_nonneg (apply_nonneg _ _) _)
  have hkey : (1 : ℝ) ≤ w (η : F) * M ^ (d - 1) := by
    refine hprod.trans ?_
    have e1 : w (η : F) ^ w.mult = w (η : F) * w (η : F) ^ (w.mult - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have e2 : M ^ (d - 1) = M ^ (w.mult - 1) * M ^ (∑ w' ∈ Finset.univ.erase w, w'.mult) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e1, e2, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (apply_nonneg _ _) (hle w) _) (pow_nonneg hM0 _)) hw0.le
  rw [inv_le_iff_one_le_mul₀ hw0, mul_comm]
  exact hkey

/-- **Denominator of an inverse.** For nonzero `η ∈ 𝒪` with `‖η‖ ≤ M`, the positive integer
`e = |N(η)|` satisfies `e ≤ M^d` and `e η⁻¹ ∈ 𝒪`. -/
theorem exists_nat_inv_integral {η : 𝓞 F} (hη : η ≠ 0) {M : ℝ}
    (hM : ‖mixedEmbedding F (η : F)‖ ≤ M) :
    ∃ e : ℕ, 0 < e ∧ (e : ℝ) ≤ M ^ Module.finrank ℚ F ∧
      IsIntegral ℤ ((e : F) * (η : F)⁻¹) := by
  set N : ℤ := Algebra.norm ℤ η with hN
  have hN0 : N ≠ 0 := Algebra.norm_ne_zero_iff.mpr hη
  refine ⟨N.natAbs, Int.natAbs_pos.mpr hN0, ?_, ?_⟩
  · have h := abs_norm_le_pow F (η : F) hM
    rw [← Algebra.coe_norm_int, ← hN] at h
    calc (N.natAbs : ℝ) = |(N : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      _ = |((N : ℚ) : ℝ)| := by rw [Rat.cast_intCast]
      _ ≤ _ := h
  · obtain ⟨c, hc⟩ := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 F) η
    rw [Algebra.intNorm_eq_norm] at hc
    have hη' : (η : F) ≠ 0 := (Subalgebra.coe_eq_zero _).not.mpr hη
    have hcF : ((N : ℤ) : F) = (η : F) * (c : F) := by
      have := congrArg (fun z : 𝓞 F => (z : F)) hc
      simpa [hN] using this
    have hval : ((N.natAbs : ℕ) : F) * (η : F)⁻¹ = (N.sign : F) * (c : F) := by
      have e1 : ((N.natAbs : ℕ) : F) = (N.sign : F) * (N : F) := by
        rw [← Int.cast_natCast, ← Int.cast_mul, Int.sign_mul_self_eq_natAbs]
      rw [e1, hcF]
      field_simp
    rw [hval]
    have hI := (isIntegral_algebraMap (R := ℤ) (A := F) (x := N.sign)).mul c.isIntegral_coe
    convert hI using 1

end Integers

end Langlands.Global.RankinSelbergGlobal.Unfolding

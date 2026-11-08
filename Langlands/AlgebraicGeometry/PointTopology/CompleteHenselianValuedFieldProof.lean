import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedField
import Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldStatement
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Instances.Rat
import Mathlib.FieldTheory.Finite.Basic

/-!
# Complete valued fields are henselian: the archimedean case

A complete nontrivially normed field that is not non-archimedean is, up to a power of its
norm, `ℝ` or `ℂ`. The norm restricted to `ℚ` is a power `|·|^s` of the usual absolute value
(Ostrowski), with `0 < s ≤ 1`. By completeness the inclusion of `ℚ` extends to `ℝ`. The power
`‖·‖^(1/s)` is again an absolute value (Artin's argument), for which `K` is a normed
`ℝ`-algebra; Gelfand–Mazur identifies it with `ℝ` or `ℂ`. Hence `K` has a ring map `φ` to `ℂ`
with `‖x‖ = ‖φ x‖^s`, and an absolute value on an algebraic extension is obtained by embedding
the extension in `ℂ`. With the non-archimedean case this proves
`CompleteHenselianValuedFieldStatement`.
-/

noncomputable section

universe u v

open Filter Topology

namespace Langlands.AlgebraicGeometry.PointTopology

namespace CompleteHenselian

variable {K : Type u} [NontriviallyNormedField K]

/-- **Complete fields with a power-isometric embedding in `ℂ` are henselian.** If `φ : K → ℂ`
satisfies `‖x‖ = ‖φ x‖^s` with `0 < s ≤ 1`, an algebraic extension embeds in `ℂ` over `K`, and
`y ↦ ‖σ y‖^s` is an absolute value extending the norm. -/
theorem isHenselianValuedField_of_rpow [CompleteSpace K] (φ : K →+* ℂ) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hφ : ∀ x, ‖x‖ = ‖φ x‖ ^ s) : IsHenselianValuedField K := by
  intro L _ _ _
  let : Algebra K ℂ := φ.toAlgebra
  let σ : L →ₐ[K] ℂ := IsAlgClosed.lift
  let w : AbsoluteValue L ℝ :=
    { toFun := fun y => ‖σ y‖ ^ s
      map_mul' := fun a b => by
        simp only [map_mul, norm_mul]
        exact Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
      nonneg' := fun _ => Real.rpow_nonneg (norm_nonneg _) _
      eq_zero' := fun y => by
        rw [Real.rpow_eq_zero (norm_nonneg _) hs0.ne', norm_eq_zero]
        exact map_eq_zero_iff σ σ.toRingHom.injective
      add_le' := fun a b => by
        simp only [map_add]
        calc ‖σ a + σ b‖ ^ s ≤ (‖σ a‖ + ‖σ b‖) ^ s :=
              Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hs0.le
          _ ≤ ‖σ a‖ ^ s + ‖σ b‖ ^ s :=
              Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hs0.le hs1 }
  have hw : ∀ x : K, w (algebraMap K L x) = ‖x‖ := by
    intro x
    change ‖σ (algebraMap K L x)‖ ^ s = ‖x‖
    rw [σ.commutes, hφ x]
    rfl
  exact ⟨w, hw, fun w' hw' => absoluteValue_eq w' w hw' hw⟩

section Archimedean

variable (K)

/-- A norm with `1 < ‖n‖` for some natural number lives in characteristic zero: in
characteristic `p`, every `n` satisfies `n ^ p = n`, so `‖n‖ ≤ 1`. -/
theorem charZero_of_one_lt_norm_natCast {n : ℕ} (hn : 1 < ‖(n : K)‖) : CharZero K := by
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | hp
  · exfalso
    have : Fact (ringChar K).Prime := ⟨hp⟩
    have hpow : ((n : K)) ^ ringChar K = (n : K) := by
      have h := congrArg (ZMod.castHom (dvd_refl (ringChar K)) K) (ZMod.pow_card (n : ZMod (ringChar K)))
      simpa only [map_pow, map_natCast] using h
    have hnorm : ‖(n : K)‖ ^ ringChar K = ‖(n : K)‖ := by rw [← norm_pow, hpow]
    have hpos : 0 < ‖(n : K)‖ := lt_trans zero_lt_one hn
    have h1 : ‖(n : K)‖ ^ (ringChar K - 1) = 1 := by
      have hp1 : ringChar K = (ringChar K - 1) + 1 := (Nat.sub_add_cancel hp.one_lt.le).symm
      rw [hp1, pow_succ] at hnorm
      exact (mul_eq_right₀ hpos.ne').mp hnorm
    have h2 : 1 < ‖(n : K)‖ ^ (ringChar K - 1) :=
      one_lt_pow₀ hn (Nat.sub_ne_zero_of_lt hp.one_lt)
    exact absurd h1 h2.ne'
  · have h0 : CharP K 0 := hp ▸ ringChar.charP K
    exact CharP.charP_to_charZero K

variable {K}

/-- The norm restricted to `ℚ`, in characteristic zero. -/
def ratAbs [CharZero K] : AbsoluteValue ℚ ℝ where
  toFun q := ‖(q : K)‖
  map_mul' a b := by simp
  nonneg' _ := norm_nonneg _
  eq_zero' q := by simp
  add_le' a b := by
    simp only [Rat.cast_add]
    exact norm_add_le _ _

theorem ratAbs_apply [CharZero K] (q : ℚ) : ratAbs (K := K) q = ‖(q : K)‖ := rfl

/-- In the archimedean case, the norm on `ℚ` is `|·|^s` for some `0 < s ≤ 1`. -/
theorem exists_rpow_of_not_ultrametric (h : ¬ IsUltrametricDist K) :
    ∃ (_ : CharZero K) (s : ℝ), 0 < s ∧ s ≤ 1 ∧ ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s := by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h
  push Not at h
  obtain ⟨n, hn⟩ := h
  have hc : CharZero K := charZero_of_one_lt_norm_natCast K hn
  refine ⟨hc, ?_⟩
  have hnb : ¬ ∀ m : ℕ, ratAbs (K := K) m ≤ 1 := by
    push Not
    exact ⟨n, by rw [ratAbs_apply, Rat.cast_natCast]; exact hn⟩
  have heq := Rat.AbsoluteValue.equiv_real_of_unbounded (f := ratAbs (K := K)) hnb
  obtain ⟨c, hc0, hcf⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp heq
  have key : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ c⁻¹ := by
    intro q
    have h1 := congrFun hcf q
    simp only [Rat.AbsoluteValue.real_eq_abs, Rat.cast_abs] at h1
    rw [ratAbs_apply] at h1
    rw [← h1, ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hc0.ne', Real.rpow_one]
  refine ⟨c⁻¹, inv_pos.mpr hc0, ?_, key⟩
  have h2 : ‖((2 : ℚ) : K)‖ ≤ 2 := by
    rw [Rat.cast_ofNat]
    calc ‖(2 : K)‖ = ‖(1 : K) + 1‖ := by norm_num
      _ ≤ ‖(1 : K)‖ + ‖(1 : K)‖ := norm_add_le _ _
      _ = 2 := by rw [norm_one]; norm_num
  rw [key] at h2
  have h3 : |((2 : ℚ) : ℝ)| = 2 := by norm_num
  rw [h3] at h2
  by_contra hlt
  push Not at hlt
  have : (2 : ℝ) ^ (1 : ℝ) < 2 ^ c⁻¹ := Real.rpow_lt_rpow_of_exponent_lt one_lt_two hlt
  rw [Real.rpow_one] at this
  linarith

end Archimedean

/-- **Artin's argument.** If `‖(m : K)‖ = m ^ s` for natural numbers `m` and `s * t = 1`
with `t ≥ 1`, then `‖·‖^t` is subadditive. -/
theorem rpow_norm_add_le {s t : ℝ} (ht : 1 ≤ t) (hst : s * t = 1)
    (hnat : ∀ m : ℕ, ‖(m : K)‖ = (m : ℝ) ^ s) (x y : K) :
    ‖x + y‖ ^ t ≤ ‖x‖ ^ t + ‖y‖ ^ t := by
  set a := ‖x‖ ^ t
  set b := ‖y‖ ^ t
  have ha : 0 ≤ a := Real.rpow_nonneg (norm_nonneg _) _
  have hb : 0 ≤ b := Real.rpow_nonneg (norm_nonneg _) _
  have hchoose : ∀ m : ℕ, ‖(m : K)‖ ^ t = m := by
    intro m
    rw [hnat, ← Real.rpow_mul (Nat.cast_nonneg _), hst, Real.rpow_one]
  -- For every `n`, `(‖x + y‖ ^ t) ^ n ≤ (n + 1) ^ (t - 1) * (a + b) ^ n`.
  have hbound : ∀ n : ℕ, (‖x + y‖ ^ t) ^ n ≤ ((n : ℝ) + 1) ^ (t - 1) * (a + b) ^ n := by
    intro n
    have hexp : (x + y) ^ n = ∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * (n.choose k : K) :=
      add_pow x y n
    have h1 : (‖x + y‖ ^ t) ^ n = ‖(x + y) ^ n‖ ^ t := by
      rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
        ← Real.rpow_mul (norm_nonneg _), mul_comm]
    rw [h1, hexp]
    calc ‖∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * (n.choose k : K)‖ ^ t
        ≤ (∑ k ∈ Finset.range (n + 1), ‖x ^ k * y ^ (n - k) * (n.choose k : K)‖) ^ t :=
          Real.rpow_le_rpow (norm_nonneg _) (norm_sum_le _ _) (by linarith)
      _ ≤ ((Finset.range (n + 1)).card : ℝ) ^ (t - 1) *
            ∑ k ∈ Finset.range (n + 1), ‖x ^ k * y ^ (n - k) * (n.choose k : K)‖ ^ t :=
          Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg _ ht (fun _ _ => norm_nonneg _)
      _ = ((n : ℝ) + 1) ^ (t - 1) * (a + b) ^ n := by
          rw [Finset.card_range, Nat.cast_add, Nat.cast_one, add_pow]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul, norm_pow, norm_pow,
            Real.mul_rpow (mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _))
              (norm_nonneg _),
            Real.mul_rpow (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _),
            hchoose, ← Real.rpow_natCast, ← Real.rpow_natCast,
            ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _), mul_comm (k : ℝ),
            mul_comm ((n - k : ℕ) : ℝ), Real.rpow_mul (norm_nonneg _), Real.rpow_mul (norm_nonneg _),
            Real.rpow_natCast, Real.rpow_natCast]
  -- Exponential growth beats polynomial growth.
  by_contra hlt
  push Not at hlt
  have hab : 0 < ‖x + y‖ ^ t := lt_of_le_of_lt (add_nonneg ha hb) hlt
  obtain ⟨N, hN⟩ := exists_nat_ge (t - 1)
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h0 | hpos
  · -- `a + b = 0`: then `x = y = 0`.
    have hx : ‖x‖ = 0 := by
      have : a = 0 := by linarith
      exact (Real.rpow_eq_zero (norm_nonneg _) (by linarith)).mp this
    have hy : ‖y‖ = 0 := by
      have : b = 0 := by linarith
      exact (Real.rpow_eq_zero (norm_nonneg _) (by linarith)).mp this
    rw [norm_eq_zero] at hx hy
    rw [hx, hy, add_zero, norm_zero, Real.zero_rpow (by linarith)] at hab
    exact lt_irrefl _ hab
  · set q := ‖x + y‖ ^ t / (a + b) with hq
    have hq1 : 1 < q := by rw [hq, one_lt_div hpos]; exact hlt
    have hlim := tendsto_pow_const_div_const_pow_of_one_lt N hq1
    have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ N / q ^ n < 1 / 2 ^ N :=
      hlim.eventually (gt_mem_nhds (by positivity))
    obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_ge_atTop 1)).exists
    have hb2 := hbound n
    have hqn : q ^ n * (a + b) ^ n = (‖x + y‖ ^ t) ^ n := by
      rw [← mul_pow, hq, div_mul_cancel₀ _ hpos.ne']
    have hpowpos : 0 < (a + b) ^ n := pow_pos hpos n
    have hle : q ^ n ≤ ((n : ℝ) + 1) ^ (t - 1) := by
      rw [← hqn] at hb2
      exact le_of_mul_le_mul_right hb2 hpowpos
    have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn2
    have h5 : q ^ n ≤ 2 ^ N * (n : ℝ) ^ N := by
      calc q ^ n ≤ ((n : ℝ) + 1) ^ (t - 1) := hle
        _ ≤ ((n : ℝ) + 1) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hN
        _ = ((n : ℝ) + 1) ^ N := Real.rpow_natCast _ _
        _ ≤ (2 * (n : ℝ)) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * (n : ℝ) ^ N := mul_pow _ _ _
    have hqpos : 0 < q ^ n := pow_pos (lt_trans zero_lt_one hq1) n
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    rw [div_lt_div_iff₀ hqpos h2N, one_mul] at hn1
    nlinarith [h5]

section Embedding

variable [CharZero K] {s : ℝ}

/-- With `‖q‖ = |q| ^ s` on `ℚ`, the inclusion of `ℚ` is uniformly continuous. -/
theorem uniformContinuous_ratCast (hs0 : 0 < s) (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s) :
    UniformContinuous (Rat.castHom K) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  refine ⟨ε ^ s⁻¹, Real.rpow_pos_of_pos hε _, fun {a b} h => ?_⟩
  rw [dist_eq_norm, ← map_sub, eq_ratCast, hrat, Rat.cast_sub]
  rw [Rat.dist_eq] at h
  calc |(a : ℝ) - b| ^ s < (ε ^ s⁻¹) ^ s :=
        Real.rpow_lt_rpow (abs_nonneg _) h hs0
    _ = ε := by rw [← Real.rpow_mul hε.le, inv_mul_cancel₀ hs0.ne', Real.rpow_one]

variable [CompleteSpace K]

/-- The extension of the inclusion of `ℚ` to `ℝ`. -/
def realHom (hs0 : 0 < s) (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s) : ℝ →+* K :=
  IsDenseInducing.extendRingHom (i := Rat.castHom ℝ) (f := Rat.castHom K)
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (uniformContinuous_ratCast hs0 hrat)

theorem realHom_ratCast (hs0 : 0 < s) (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s) (q : ℚ) :
    realHom hs0 hrat (q : ℝ) = (q : K) :=
  (Rat.isUniformEmbedding_coe_real.isUniformInducing.isDenseInducing Rat.denseRange_cast).extend_eq
    (uniformContinuous_ratCast hs0 hrat).continuous q

theorem continuous_realHom (hs0 : 0 < s) (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s) :
    Continuous (realHom hs0 hrat) :=
  (uniformContinuous_uniformly_extend Rat.isUniformEmbedding_coe_real.isUniformInducing
    Rat.denseRange_cast (uniformContinuous_ratCast hs0 hrat)).continuous

theorem norm_realHom (hs0 : 0 < s) (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s) (r : ℝ) :
    ‖realHom hs0 hrat r‖ = |r| ^ s := by
  refine Rat.denseRange_cast.induction_on r
    (isClosed_eq (continuous_norm.comp (continuous_realHom hs0 hrat))
      (continuous_abs.rpow_const fun _ => Or.inr hs0.le)) fun q => ?_
  rw [realHom_ratCast, hrat]

/-- The absolute value `‖·‖ ^ (1/s)`. -/
def archAbs (hs0 : 0 < s) (hs1 : s ≤ 1) (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s) :
    AbsoluteValue K ℝ where
  toFun x := ‖x‖ ^ s⁻¹
  map_mul' a b := by
    simp only [norm_mul]
    exact Real.mul_rpow (norm_nonneg _) (norm_nonneg _)
  nonneg' _ := Real.rpow_nonneg (norm_nonneg _) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero (norm_nonneg _) (inv_pos.mpr hs0).ne', norm_eq_zero]
  add_le' x y := rpow_norm_add_le (one_le_inv₀ hs0 |>.mpr hs1) (mul_inv_cancel₀ hs0.ne')
    (fun m => by simpa using hrat m) x y

omit [CharZero K] [CompleteSpace K] in
theorem archAbs_apply (hs0 : 0 < s) (hs1 : s ≤ 1) (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s)
    (x : K) : archAbs hs0 hs1 hrat x = ‖x‖ ^ s⁻¹ := rfl

theorem archAbs_realHom (hs0 : 0 < s) (hs1 : s ≤ 1) (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s)
    (r : ℝ) : archAbs hs0 hs1 hrat (realHom hs0 hrat r) = |r| := by
  rw [archAbs_apply, norm_realHom, ← Real.rpow_mul (abs_nonneg _), mul_inv_cancel₀ hs0.ne',
    Real.rpow_one]

omit [CharZero K] [CompleteSpace K] in
theorem norm_eq_archAbs_rpow (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s) (x : K) :
    ‖x‖ = archAbs hs0 hs1 hrat x ^ s := by
  rw [archAbs_apply, ← Real.rpow_mul (norm_nonneg _), inv_mul_cancel₀ hs0.ne', Real.rpow_one]

/-- In the archimedean case `K` has a ring map to `ℂ` with `‖x‖ = ‖φ x‖ ^ s`. -/
theorem exists_complex_rpow (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hrat : ∀ q : ℚ, ‖(q : K)‖ = |(q : ℝ)| ^ s) :
    ∃ φ : K →+* ℂ, ∀ x, ‖x‖ = ‖φ x‖ ^ s := by
  set v := archAbs hs0 hs1 hrat
  set ψ := realHom hs0 hrat
  let A : Algebra ℝ (WithAbs v) := ((WithAbs.equiv v).symm.toRingHom.comp ψ).toAlgebra
  have halg : ∀ r : ℝ, algebraMap ℝ (WithAbs v) r = WithAbs.toAbs v (ψ r) := fun _ => rfl
  let NA : NormedAlgebra ℝ (WithAbs v) :=
    { A with
      norm_smul_le := fun r x => by
        rw [Algebra.smul_def, halg, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_mul,
          WithAbs.ofAbs_toAbs, map_mul, archAbs_realHom, WithAbs.norm_eq_apply_ofAbs,
          Real.norm_eq_abs] }
  rcases NormedAlgebra.Real.nonempty_algEquiv_or (WithAbs v) with hα | hβ
  · obtain ⟨α⟩ := hα
    refine ⟨Complex.ofRealHom.comp (α.toRingHom.comp (WithAbs.equiv v).symm.toRingHom),
      fun x => ?_⟩
    have hx : x = ψ (α (WithAbs.toAbs v x)) := by
      have h := α.symm_apply_apply (WithAbs.toAbs v x)
      have h2 : α.symm (α (WithAbs.toAbs v x)) =
          algebraMap ℝ (WithAbs v) (α (WithAbs.toAbs v x)) := by
        rw [← AlgEquiv.commutes α.symm]
        rfl
      rw [h2, halg] at h
      exact (WithAbs.toAbs_injective (v := v) h).symm
    rw [norm_eq_archAbs_rpow hs0 hs1 hrat x]
    congr 1
    conv_lhs => rw [hx]
    rw [archAbs_realHom]
    simp [RingHom.comp_apply, Complex.norm_real]
  · obtain ⟨β⟩ := hβ
    let w : AbsoluteValue ℂ ℝ :=
      { toFun := fun z => v (WithAbs.ofAbs (β.symm z))
        map_mul' := fun a b => by simp
        nonneg' := fun _ => v.nonneg _
        eq_zero' := fun z => by simp
        add_le' := fun a b => by simpa using v.add_le' _ _ }
    let n : AbsoluteValue ℂ ℝ := MulRingNorm.toAbsoluteValue (NormedField.toMulRingNorm ℂ)
    have hw : ∀ r : ℝ, w (algebraMap ℝ ℂ r) = ‖r‖ := by
      intro r
      change v (WithAbs.ofAbs (β.symm (algebraMap ℝ ℂ r))) = ‖r‖
      rw [AlgEquiv.commutes, halg, WithAbs.ofAbs_toAbs, archAbs_realHom, Real.norm_eq_abs]
    have hn : ∀ r : ℝ, n (algebraMap ℝ ℂ r) = ‖r‖ := fun r => by
      change ‖(algebraMap ℝ ℂ r)‖ = ‖r‖
      simp
    have : Algebra.IsAlgebraic ℝ ℂ := Algebra.IsAlgebraic.of_finite ℝ ℂ
    have hwn := absoluteValue_eq w n hw hn
    refine ⟨β.toRingHom.comp (WithAbs.equiv v).symm.toRingHom, fun x => ?_⟩
    rw [norm_eq_archAbs_rpow hs0 hs1 hrat x]
    congr 1
    have h1 := congrArg (fun f : AbsoluteValue ℂ ℝ => f (β (WithAbs.toAbs v x))) hwn
    change v (WithAbs.ofAbs (β.symm (β (WithAbs.toAbs v x)))) = _ at h1
    rw [AlgEquiv.symm_apply_apply, WithAbs.ofAbs_toAbs] at h1
    rw [h1]
    rfl

end Embedding

/-- **Complete archimedean fields are henselian.** -/
theorem isHenselianValuedField_of_not_isUltrametricDist [CompleteSpace K]
    (h : ¬ IsUltrametricDist K) : IsHenselianValuedField K := by
  obtain ⟨_, s, hs0, hs1, hrat⟩ := exists_rpow_of_not_ultrametric h
  obtain ⟨φ, hφ⟩ := exists_complex_rpow hs0 hs1 hrat
  exact isHenselianValuedField_of_rpow φ hs0 hs1 hφ

end CompleteHenselian

/-- **Complete valued fields are henselian** (Conrad, printed p.14). -/
theorem completeHenselianValuedField : CompleteHenselianValuedFieldStatement.{u} := by
  intro K _ _
  by_cases h : IsUltrametricDist K
  · exact CompleteHenselian.isHenselianValuedField_of_isUltrametricDist
  · exact CompleteHenselian.isHenselianValuedField_of_not_isUltrametricDist h


end Langlands.AlgebraicGeometry.PointTopology

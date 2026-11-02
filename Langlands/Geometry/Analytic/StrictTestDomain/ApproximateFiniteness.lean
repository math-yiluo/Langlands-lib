import Langlands.Geometry.Analytic.SpectralPowerBoundProof
import Langlands.Geometry.Analytic.AffinoidUnitNorm
import Langlands.Geometry.Analytic.FiniteBanachModule
import Langlands.Geometry.Analytic.TateSeries
import Langlands.Geometry.Analytic.TateUniversal
import Langlands.Geometry.Analytic.StrictTestDomain.PairTest

/-! # Finiteness from close approximations of the coordinates -/

noncomputable section

open Filter Topology

universe u

namespace Langlands.Analytic

/-- Approximate preimages with linearly controlled norms give exact preimages:
the successive corrections are summed in the complete source. -/
theorem surjective_of_approx_preimage {V W F : Type*} [NormedAddCommGroup V]
    [CompleteSpace V] [NormedAddCommGroup W] [FunLike F V W] [AddMonoidHomClass F V W]
    (Φ : F) (hΦ : Continuous Φ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ w : W, ∃ v : V, ‖v‖ ≤ C * ‖w‖ ∧ ‖w - Φ v‖ ≤ ‖w‖ / 2) :
    Function.Surjective Φ := by
  intro w
  choose g hg using h
  let r : W → W := fun z => z - Φ (g z)
  have hr : ∀ n : ℕ, ‖r^[n] w‖ ≤ (1 / 2) ^ n * ‖w‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ]
      have h2 := (hg (r^[n] w)).2
      change ‖r^[n] w - Φ (g (r^[n] w))‖ ≤ _
      linarith
  let u : ℕ → V := fun n => g (r^[n] w)
  have hu : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖w‖) := fun n =>
    calc ‖u n‖ ≤ C * ‖r^[n] w‖ := (hg _).1
      _ ≤ C * ((1 / 2) ^ n * ‖w‖) := mul_le_mul_of_nonneg_left (hr n) hC
      _ = (1 / 2) ^ n * (C * ‖w‖) := by ring
  have hsum : Summable fun n => ‖u n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hu
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _)
  have su : Summable u := hsum.of_norm
  refine ⟨∑' n, u n, ?_⟩
  have hpartial : ∀ n : ℕ, Φ (∑ k ∈ Finset.range n, u k) = w - r^[n] w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ih, Function.iterate_succ_apply']
      change w - r^[n] w + Φ (g (r^[n] w)) = w - (r^[n] w - Φ (g (r^[n] w)))
      abel
  have L₁ : Tendsto (fun n => Φ (∑ k ∈ Finset.range n, u k)) atTop
      (𝓝 (Φ (∑' n, u n))) :=
    (hΦ.tendsto _).comp su.hasSum.tendsto_sum_nat
  simp only [hpartial] at L₁
  have L₂ : Tendsto (fun n => w - r^[n] w) atTop (𝓝 (w - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hr ?_
    rw [← zero_mul ‖w‖]
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul
      tendsto_const_nhds
  rw [sub_zero] at L₂
  exact tendsto_nhds_unique L₁ L₂

/-- In a normed ring whose unit has norm at most one, a finite product of factors
of norm at most `D` has norm at most `D` to the number of factors. -/
theorem norm_prod_le_pow {ι B : Type*} [NormedCommRing B] (h1 : ‖(1 : B)‖ ≤ 1)
    (s : Finset ι) (y : ι → B) {D : ℝ} (hD : 0 ≤ D) (hy : ∀ k ∈ s, ‖y k‖ ≤ D) :
    ‖∏ k ∈ s, y k‖ ≤ D ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul (hy a (Finset.mem_insert_self a s))
      (ih fun k hk => hy k (Finset.mem_insert_of_mem hk)) (norm_nonneg _) hD)

/-- In an ultrametric normed ring whose unit has norm at most one, products of
factors that are pairwise `η`-close and bounded by `D ≥ 1` are `η D ^ card`-close. -/
theorem norm_prod_sub_prod_le {ι B : Type*} [NormedCommRing B] [IsUltrametricDist B]
    (h1 : ‖(1 : B)‖ ≤ 1) (s : Finset ι) (x y : ι → B) {D η : ℝ} (hD : 1 ≤ D)
    (hη : 0 ≤ η) (hx : ∀ k ∈ s, ‖x k‖ ≤ D) (hy : ∀ k ∈ s, ‖y k‖ ≤ D)
    (hxy : ∀ k ∈ s, ‖x k - y k‖ ≤ η) :
    ‖∏ k ∈ s, x k - ∏ k ∈ s, y k‖ ≤ η * D ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hη
  | insert a s ha ih =>
    have hs : ∀ k ∈ s, k ∈ insert a s := fun k hk => Finset.mem_insert_of_mem hk
    have ih' := ih (fun k hk => hx k (hs k hk)) (fun k hk => hy k (hs k hk))
      (fun k hk => hxy k (hs k hk))
    have hprod := norm_prod_le_pow h1 s y (by linarith) fun k hk => hy k (hs k hk)
    have hxa := hx a (Finset.mem_insert_self a s)
    have hxya := hxy a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have heq : x a * ∏ k ∈ s, x k - y a * ∏ k ∈ s, y k =
        x a * (∏ k ∈ s, x k - ∏ k ∈ s, y k) + (x a - y a) * ∏ k ∈ s, y k := by ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · calc ‖x a * (∏ k ∈ s, x k - ∏ k ∈ s, y k)‖
          ≤ ‖x a‖ * ‖∏ k ∈ s, x k - ∏ k ∈ s, y k‖ := norm_mul_le _ _
        _ ≤ D * (η * D ^ s.card) := mul_le_mul hxa ih' (norm_nonneg _) (by linarith)
        _ = η * D ^ (s.card + 1) := by ring
    · calc ‖(x a - y a) * ∏ k ∈ s, y k‖ ≤ ‖x a - y a‖ * ‖∏ k ∈ s, y k‖ := norm_mul_le _ _
        _ ≤ η * D ^ s.card := mul_le_mul hxya hprod (norm_nonneg _) hη
        _ ≤ η * D ^ (s.card + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.le_succ _)) hη

/-- The binomial expansion of `(x + y) ^ n`, split into the terms whose exponent
of `x` is below `N` and the remaining terms; binomial coefficients act as scalars. -/
theorem add_pow_eq_sum_range_add_sum_Ico {K B : Type*} [CommSemiring K] [CommSemiring B]
    [Algebra K B] (x y : B) (n N : ℕ) :
    (x + y) ^ n = ∑ j ∈ Finset.range N, (n.choose j : K) • (x ^ j * y ^ (n - j)) +
      ∑ j ∈ Finset.Ico N (n + N + 1), (n.choose j : K) • (x ^ j * y ^ (n - j)) := by
  have hterm : ∀ j, x ^ j * y ^ (n - j) * (n.choose j : B) =
      (n.choose j : K) • (x ^ j * y ^ (n - j)) := fun j => by
    rw [Nat.cast_smul_eq_nsmul K, nsmul_eq_mul']
  rw [Finset.sum_range_add_sum_Ico _ (by omega), add_pow]
  simp_rw [hterm]
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
  intro j _ hj
  rw [Finset.mem_range, not_lt] at hj
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]

namespace PresentedStrictAffinoidAlgebra

open StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Over a nontrivially valued field, if every point of the spectrum is below one
on `b`, then all sufficiently high powers of `b` have norm at most any given
positive bound. -/
theorem exists_norm_pow_le_of_spectrum_lt_one (hK : ∃ c : K, 1 < ‖c‖)
    (P : PresentedStrictAffinoidAlgebra K) (b : P)
    (hb : ∀ y : BanachSpectrum P, y b < 1) {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ‖b ^ n‖ ≤ η := by
  obtain ⟨r, hr1, hr⟩ : ∃ r : ℝ, r < 1 ∧ ∀ y : BanachSpectrum P, y b ≤ r := by
    rcases isEmpty_or_nonempty (BanachSpectrum P) with hP | hP
    · exact ⟨0, zero_lt_one, fun y => (IsEmpty.false y).elim⟩
    · obtain ⟨y₀, -, hy₀⟩ := IsCompact.exists_isMaxOn
        (isCompact_univ : IsCompact (Set.univ : Set (BanachSpectrum P))) Set.univ_nonempty
        (BanachSpectrum.evaluation (A := P) b).continuous.continuousOn
      exact ⟨y₀ b, hb y₀, fun y => hy₀ (Set.mem_univ y)⟩
  obtain ⟨c, hc⟩ := hK
  have hc0 : (0 : ℝ) < ‖c‖ := zero_lt_one.trans hc
  have hcne : c ≠ 0 := norm_pos_iff.mp hc0
  have hl0 : 0 < ‖c‖⁻¹ := inv_pos.mpr hc0
  have hl1 : ‖c‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hl0 hr1
  have he : ∀ y : BanachSpectrum P, y (c • b ^ n) ≤ 1 := by
    intro y
    have hy0 : 0 ≤ y b := apply_nonneg y.toMulRingSeminorm b
    rw [Algebra.smul_def, map_mul, map_pow, BanachSpectrum.algebraMap_apply]
    calc ‖c‖ * y b ^ n ≤ ‖c‖ * ‖c‖⁻¹ :=
          mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hy0 (hr y) n).trans hn.le)
            (norm_nonneg c)
      _ = 1 := mul_inv_cancel₀ hc0.ne'
  obtain ⟨C₁, hC₁, hC₁b⟩ := hasBoundedPowers_of_spectrum_le_one P (c • b ^ n) he
  obtain ⟨C₂, hC₂, hC₂b⟩ := hasBoundedPowers_of_spectrum_le_one P b fun y => (hb y).le
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, pow_zero] at hn
      exact absurd hn (not_lt.mpr hl1.le)
    · exact h
  obtain ⟨j₀, hj₀⟩ := exists_pow_lt_of_lt_one (div_pos hη (mul_pos hC₁ hC₂)) hl1
  refine ⟨n * j₀, fun N hN => ?_⟩
  have hpow : ∀ j : ℕ, ‖b ^ (n * j)‖ ≤ ‖c‖⁻¹ ^ j * C₁ := by
    intro j
    have h : b ^ (n * j) = c⁻¹ ^ j • (c • b ^ n) ^ j := by
      rw [smul_pow, smul_smul, ← mul_pow, inv_mul_cancel₀ hcne, one_pow, one_smul,
        ← pow_mul]
    rw [h, norm_smul, norm_pow, norm_inv]
    exact mul_le_mul_of_nonneg_left (hC₁b j) (pow_nonneg hl0.le j)
  have hdiv : j₀ ≤ N / n := (Nat.le_div_iff_mul_le hn0).mpr (by rw [mul_comm]; exact hN)
  calc ‖b ^ N‖ = ‖b ^ (n * (N / n)) * b ^ (N % n)‖ := by rw [← pow_add, Nat.div_add_mod]
    _ ≤ ‖b ^ (n * (N / n))‖ * ‖b ^ (N % n)‖ := norm_mul_le _ _
    _ ≤ ‖c‖⁻¹ ^ (N / n) * C₁ * C₂ :=
        mul_le_mul (hpow _) (hC₂b _) (norm_nonneg _)
          (mul_nonneg (pow_nonneg hl0.le _) hC₁.le)
    _ ≤ ‖c‖⁻¹ ^ j₀ * C₁ * C₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one hl0.le hl1.le hdiv) hC₁.le) hC₂.le
    _ ≤ η := by
        have h := (lt_div_iff₀ (mul_pos hC₁ hC₂)).mp hj₀
        rw [mul_assoc]
        exact h.le

/-- **Finiteness from close approximations of the coordinates.** Let `K` be complete
and nontrivially valued and `i : A → B` a bounded map of presented strict affinoid
algebras. Suppose that for every coordinate `t_k` of `B` there is `a_k ∈ A` with
`x (a_k) ≤ 1` at every point `x` of `M(A)` and `y (t_k - i a_k) < 1` at every point
`y` of `M(B)`. Then `i` is finite. -/
theorem finite_of_spectrum_coordinate_sub_lt_one (hK : ∃ c : K, 1 < ‖c‖)
    {A B : PresentedStrictAffinoidAlgebra K} (i : BoundedAlgHom K A B)
    (a : Fin B.arity → A) (ha : ∀ x : BanachSpectrum A, ∀ k, x (a k) ≤ 1)
    (hc : ∀ y : BanachSpectrum B, ∀ k, y (coordinate K B k - i (a k)) < 1) :
    i.toAlgHom.toRingHom.Finite := by
  classical
  let t : Fin B.arity → B := fun k => coordinate K B k
  let c : Fin B.arity → B := fun k => coordinate K B k - i (a k)
  have htc : ∀ k, t k = c k + i (a k) := fun k => (sub_add_cancel _ _).symm
  -- Uniform bounds for the powers of `a k`, the powers of `c k`, and the map `i`.
  have hpa : ∀ k, ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, ‖a k ^ p‖ ≤ C := fun k =>
    hasBoundedPowers_of_spectrum_le_one A (a k) fun x => ha x k
  have hpc : ∀ k, ∃ C : ℝ, 0 < C ∧ ∀ p : ℕ, ‖c k ^ p‖ ≤ C := fun k =>
    hasBoundedPowers_of_spectrum_le_one B (c k) fun y => (hc y k).le
  choose Ca' hCa' hCab' using hpa
  choose Cc' hCc' hCcb' using hpc
  obtain ⟨Ci', hCi', hCib'⟩ := i.bounded
  obtain ⟨Ca, hCa1, hCa⟩ : ∃ Ca : ℝ, 1 ≤ Ca ∧ ∀ k p, ‖a k ^ p‖ ≤ Ca :=
    ⟨1 + ∑ k, Ca' k, le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => (hCa' k).le),
      fun k p => (hCab' k p).trans ((Finset.single_le_sum (fun k _ => (hCa' k).le)
        (Finset.mem_univ k)).trans (le_add_of_nonneg_left zero_le_one))⟩
  obtain ⟨Cc, hCc1, hCc⟩ : ∃ Cc : ℝ, 1 ≤ Cc ∧ ∀ k p, ‖c k ^ p‖ ≤ Cc :=
    ⟨1 + ∑ k, Cc' k, le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => (hCc' k).le),
      fun k p => (hCcb' k p).trans ((Finset.single_le_sum (fun k _ => (hCc' k).le)
        (Finset.mem_univ k)).trans (le_add_of_nonneg_left zero_le_one))⟩
  obtain ⟨Ci, hCi1, hCi⟩ : ∃ Ci : ℝ, 1 ≤ Ci ∧ ∀ z, ‖i z‖ ≤ Ci * ‖z‖ :=
    ⟨1 + Ci', le_add_of_nonneg_right hCi'.le, fun z => (hCib' z).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg z))⟩
  have hCa0 : 0 ≤ Ca := zero_le_one.trans hCa1
  have hCiCa : 0 < Ci * Ca := mul_pos (zero_lt_one.trans_le hCi1) (zero_lt_one.trans_le hCa1)
  have hy : ∀ k p, ‖i (a k) ^ p‖ ≤ Ci * Ca := fun k p => by
    rw [← map_pow i.toAlgHom]
    exact (hCi _).trans (mul_le_mul_of_nonneg_left (hCa k p) (zero_le_one.trans hCi1))
  -- The threshold `η` and the power `N` beyond which all `c k ^ p` are `η`-small.
  obtain ⟨D, hD1, hDdef⟩ : ∃ D : ℝ, 1 ≤ D ∧ D = Cc * (Ci * Ca) :=
    ⟨Cc * (Ci * Ca), one_le_mul_of_one_le_of_one_le hCc1
      (one_le_mul_of_one_le_of_one_le hCi1 hCa1), rfl⟩
  have hDm : 0 < D ^ B.arity := pow_pos (zero_lt_one.trans_le hD1) _
  obtain ⟨η, hη0, hηeq⟩ : ∃ η : ℝ, 0 < η ∧ η * (Ci * Ca) * D ^ B.arity = 1 / 4 :=
    ⟨(4 * (Ci * Ca) * D ^ B.arity)⁻¹, inv_pos.mpr (mul_pos (mul_pos four_pos hCiCa) hDm),
      by field_simp⟩
  have hη1 : η ≤ 1 := by
    have h1 : 1 ≤ Ci * Ca * D ^ B.arity :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCi1 hCa1)
        (one_le_pow₀ hD1)
    have h2 : η ≤ η * (Ci * Ca * D ^ B.arity) := le_mul_of_one_le_right hη0.le h1
    rw [← mul_assoc, hηeq] at h2
    linarith
  have hηD : η * (Ci * Ca) ≤ D := by
    rw [hDdef]
    exact mul_le_mul_of_nonneg_right (hη1.trans hCc1) hCiCa.le
  choose N₀ hN₀ using fun k =>
    exists_norm_pow_le_of_spectrum_lt_one hK B (c k) (fun y => hc y k) hη0
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k p, N ≤ p → ‖c k ^ p‖ ≤ η :=
    ⟨∑ k, N₀ k, fun k p hp => hN₀ k p
      ((Finset.single_le_sum (fun k _ => Nat.zero_le (N₀ k)) (Finset.mem_univ k)).trans hp)⟩
  -- One-variable approximations of the powers of the coordinates.
  let P : Fin B.arity → ℕ → B := fun k n =>
    ∑ j : Fin N, ((n.choose j : ℕ) : K) • (c k ^ (j : ℕ) * i (a k) ^ (n - j))
  have hterm : ∀ k n j,
      ‖((n.choose j : ℕ) : K) • (c k ^ j * i (a k) ^ (n - j))‖ ≤ ‖c k ^ j‖ * (Ci * Ca) := by
    intro k n j
    rw [norm_smul]
    calc ‖((n.choose j : ℕ) : K)‖ * ‖c k ^ j * i (a k) ^ (n - j)‖
        ≤ 1 * (‖c k ^ j‖ * ‖i (a k) ^ (n - j)‖) :=
          mul_le_mul (IsUltrametricDist.norm_natCast_le_one K _) (norm_mul_le _ _)
            (norm_nonneg _) zero_le_one
      _ ≤ ‖c k ^ j‖ * (Ci * Ca) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left (hy k _) (norm_nonneg _)
  have hP : ∀ k n, ‖P k n‖ ≤ D := fun k n => by
    rw [hDdef]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (zero_le_one.trans hCc1) hCiCa.le) fun j _ =>
        (hterm k n j).trans (mul_le_mul_of_nonneg_right (hCc k j) hCiCa.le)
  have hR : ∀ k n, ‖t k ^ n - P k n‖ ≤ η * (Ci * Ca) := fun k n => by
    rw [htc k, add_pow_eq_sum_range_add_sum_Ico (K := K) (c k) (i (a k)) n N,
      ← Fin.sum_univ_eq_sum_range, add_sub_cancel_left]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_pos hη0 hCiCa).le
      fun j hj => (hterm k n j).trans
        (mul_le_mul_of_nonneg_right (hN k j (Finset.mem_Ico.mp hj).1) hCiCa.le)
  have ht : ∀ k n, ‖t k ^ n‖ ≤ D := fun k n => by
    have h := IsUltrametricDist.norm_add_le_max (P k n) (t k ^ n - P k n)
    rw [add_sub_cancel] at h
    exact h.trans (max_le (hP k n) ((hR k n).trans hηD))
  -- Expansion of products of the one-variable approximations.
  let cpow : (Fin B.arity → Fin N) → B := fun β => ∏ k, c k ^ (β k : ℕ)
  let coef : (Fin B.arity →₀ ℕ) → (Fin B.arity → Fin N) → A := fun d β =>
    ∏ k, (((d k).choose (β k) : ℕ) : K) • a k ^ (d k - β k)
  have hcoef : ∀ d β, ‖coef d β‖ ≤ Ca ^ B.arity := fun d β => by
    have h := norm_prod_le_pow (quotient_norm_one_le A) Finset.univ
      (fun k => (((d k).choose (β k) : ℕ) : K) • a k ^ (d k - β k)) hCa0 fun k _ => by
        rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (IsUltrametricDist.norm_natCast_le_one K _)).trans (hCa k _)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  have hexpand : ∀ d : Fin B.arity →₀ ℕ,
      ∏ k, P k (d k) = ∑ β : Fin B.arity → Fin N, i (coef d β) * cpow β := by
    intro d
    simp only [P]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [coef, cpow]
    rw [map_prod i.toAlgHom, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_smul i.toAlgHom, map_pow i.toAlgHom, smul_mul_assoc, mul_comm]
  have hmono : ∀ d : Fin B.arity →₀ ℕ,
      ‖monomialValue (Fin B.arity) B t d -
        ∑ β : Fin B.arity → Fin N, i (coef d β) * cpow β‖ ≤ 1 / 4 := by
    intro d
    rw [monomialValue_fintype, ← hexpand d, ← hηeq]
    have h := norm_prod_sub_prod_le (quotient_norm_one_le B) Finset.univ
      (fun k => t k ^ d k) (fun k => P k (d k)) hD1 (mul_pos hη0 hCiCa).le
      (fun k _ => ht k _) (fun k _ => hP k _) (fun k _ => hR k _)
    rwa [Finset.card_univ, Fintype.card_fin] at h
  -- The coefficient map on the monomials in `c` with exponents below `N`.
  let e := Fintype.equivFin (Fin B.arity → Fin N)
  let bs : Fin (Fintype.card (Fin B.arity → Fin N)) → B := fun l => cpow (e.symm l)
  let Φ := i.coefficientMap bs
  have hΦ : ∀ G : (Fin B.arity → Fin N) → A,
      Φ (fun l => G (e.symm l)) = ∑ β, i (G β) * cpow β := by
    intro G
    rw [BoundedAlgHom.coefficientMap_apply]
    exact e.symm.sum_comp (fun β => i (G β) * cpow β)
  have happrox : ∀ b : B, ∃ G : Fin (Fintype.card (Fin B.arity → Fin N)) → A,
      ‖G‖ ≤ (2 * Ca ^ B.arity) * ‖b‖ ∧ ‖b - Φ G‖ ≤ ‖b‖ / 2 := by
    intro b
    rcases eq_or_ne b 0 with rfl | hb
    · exact ⟨0, by simp, by simp⟩
    have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr hb
    obtain ⟨F, hF, hFb⟩ := exists_representative_norm_lt K B b hb0
    have hlim : Tendsto (fun s : Finset (Fin B.arity →₀ ℕ) =>
        ∑ d ∈ s, monomial _ K d (MvPowerSeries.coeff d (series _ K F))) atTop (𝓝 F) :=
      hasSum_monomials _ K F
    obtain ⟨S, hS⟩ := Metric.tendsto_atTop.mp hlim (‖b‖ / 2) (by positivity)
    have hS' := hS S le_rfl
    rw [dist_comm, dist_eq_norm] at hS'
    let f : (Fin B.arity →₀ ℕ) → K := fun d => MvPowerSeries.coeff d (series _ K F)
    have hf : ∀ d, ‖f d‖ ≤ ‖F‖ := fun d => norm_coeff_le _ K F d
    let G : (Fin B.arity → Fin N) → A := fun β => ∑ d ∈ S, f d • coef d β
    have hC0 : 0 ≤ (2 * Ca ^ B.arity) * ‖b‖ :=
      mul_nonneg (mul_nonneg zero_le_two (pow_nonneg hCa0 _)) (norm_nonneg b)
    refine ⟨fun l => G (e.symm l), ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg hC0).mpr fun l => ?_
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC0 fun d _ => ?_
      rw [norm_smul]
      calc ‖f d‖ * ‖coef d (e.symm l)‖ ≤ ‖F‖ * Ca ^ B.arity :=
            mul_le_mul (hf d) (hcoef d _) (norm_nonneg _) (norm_nonneg _)
        _ ≤ (2 * ‖b‖) * Ca ^ B.arity :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hCa0 _)
        _ = (2 * Ca ^ B.arity) * ‖b‖ := by ring
    · have h1 : ∑ β, i (G β) * cpow β = ∑ d ∈ S, f d • ∑ β, i (coef d β) * cpow β := by
        simp only [G, map_sum i.toAlgHom, map_smul i.toAlgHom, Finset.sum_mul,
          smul_mul_assoc, Finset.smul_sum]
        exact Finset.sum_comm
      have h2 : presentationMap K B (∑ d ∈ S, monomial _ K d (f d)) =
          ∑ d ∈ S, f d • monomialValue (Fin B.arity) B t d := by
        rw [map_sum (presentationMap K B).toAlgHom]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Algebra.smul_def]
        exact map_monomial (Fin B.arity) K B (presentationMap K B) d (f d)
      have hsplit : b - ∑ β, i (G β) * cpow β =
          presentationMap K B (F - ∑ d ∈ S, monomial _ K d (f d)) +
            ∑ d ∈ S, f d • (monomialValue (Fin B.arity) B t d -
              ∑ β, i (coef d β) * cpow β) := by
        rw [h1, map_sub (presentationMap K B).toAlgHom, h2, hF]
        simp only [smul_sub, Finset.sum_sub_distrib]
        abel
      rw [hΦ, hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · calc ‖presentationMap K B (F - ∑ d ∈ S, monomial _ K d (f d))‖
            = ‖Ideal.Quotient.mk B.ideal (F - ∑ d ∈ S, monomial _ K d (f d))‖ := rfl
          _ ≤ ‖F - ∑ d ∈ S, monomial _ K d (f d)‖ := Ideal.Quotient.norm_mk_le B.ideal _
          _ ≤ ‖b‖ / 2 := hS'.le
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
          fun d _ => ?_
        rw [norm_smul]
        calc ‖f d‖ * ‖monomialValue (Fin B.arity) B t d -
              ∑ β, i (coef d β) * cpow β‖ ≤ ‖F‖ * (1 / 4) :=
            mul_le_mul (hf d) (hmono d) (norm_nonneg _) (norm_nonneg _)
          _ ≤ ‖b‖ / 2 := by linarith
  have hsurj : Function.Surjective Φ :=
    surjective_of_approx_preimage Φ Φ.continuous
      (mul_nonneg zero_le_two (pow_nonneg hCa0 _)) happrox
  exact i.finite_iff_exists_surjective_coefficientMap.mpr ⟨_, bs, hsurj⟩

end PresentedStrictAffinoidAlgebra

end Langlands.Analytic

import Langlands.Representation.Classification.ParabolicConeAuxiliaryStatement
import Langlands.Group.GL.AdjacentMergeShape

/-!
# Uniqueness of the numerical block cone

Proof of `Langlands.GLBlockConeUniquenessStatement`. For one set of numerical witnesses
`(C, q, t)` put `a i = t (q i)` and form the residuals `e i = r i - B.size i * a i`. Their
fibre sums vanish and their inclusive prefix sums are nonpositive, so summation by parts
gives `∑ e i * v i ≤ 0` for every antitone `v`, with equality for `v = a`. Comparing two
sets of witnesses yields `∑ B.size i * (a i - b i) ^ 2 ≤ 0`, hence `a = b`. Strict
antitonicity then shows that both labellings induce the same order on the fine blocks,
so they agree up to the cast of their equal lengths, and the fibre sizes agree.
-/

namespace Langlands

open Finset GeneralLinear

namespace ParabolicConeUniqueness

variable {L : ℕ}

/-- Summation by parts: residuals with nonpositive inclusive prefix sums and zero total
pair nonpositively with every antitone vector. -/
theorem sum_mul_nonpos_of_antitone (e v : Fin L → ℝ) (hv : Antitone v)
    (hpre : ∀ i, ∑ k ∈ univ.filter (fun k => k ≤ i), e k ≤ 0)
    (htot : ∑ k, e k = 0) : ∑ k, e k * v k ≤ 0 := by
  -- Partial sums over the first `m` blocks, against any lower bound `c` of `v` on them.
  have key : ∀ m, m ≤ L → ∀ c : ℝ, (∀ k : Fin L, k.val < m → c ≤ v k) →
      ∑ k ∈ univ.filter (fun k : Fin L => k.val < m), e k * v k ≤
        c * ∑ k ∈ univ.filter (fun k : Fin L => k.val < m), e k := by
    intro m
    induction m with
    | zero =>
      intro _ c _
      simp
    | succ m ih =>
      intro hm c hc
      let p : Fin L := ⟨m, hm⟩
      have hset : univ.filter (fun k : Fin L => k.val < m + 1) =
          insert p (univ.filter (fun k : Fin L => k.val < m)) := by
        ext k
        simp only [mem_filter, mem_univ, true_and, mem_insert, p, Fin.ext_iff]
        omega
      have hp : p ∉ univ.filter (fun k : Fin L => k.val < m) := by simp [p]
      have hpre' : univ.filter (fun k : Fin L => k.val < m + 1) =
          univ.filter (fun k : Fin L => k ≤ p) := by
        ext k
        simp only [mem_filter, mem_univ, true_and, Fin.le_def, p]
        omega
      have hP : ∑ k ∈ univ.filter (fun k : Fin L => k.val < m + 1), e k ≤ 0 := by
        rw [hpre']
        exact hpre p
      have hih := ih (by omega) (v p) fun k hk => hv (show k ≤ p from Fin.le_def.2 hk.le)
      have hcp : c ≤ v p := hc p (by simp [p])
      rw [hset, sum_insert hp] at hP
      rw [hset, sum_insert hp, sum_insert hp]
      nlinarith [mul_nonneg (sub_nonneg.2 hcp) (neg_nonneg.2 hP)]
  obtain ⟨c, hc⟩ := (Set.finite_range v).bddBelow
  have huniv : univ.filter (fun k : Fin L => k.val < L) = univ := by
    ext k
    simp
  have h := key L le_rfl c fun k _ => hc ⟨k, rfl⟩
  rw [huniv, htot, mul_zero] at h
  exact h

section Witness

variable {n : ℕ} {B C : BlockShape n} {r : Fin B.length → ℝ}
  {q : Fin B.length → Fin C.length} {t : Fin C.length → ℝ}

/-- The residual of `r` against the exponent of its coarse block. -/
abbrev residual (B : BlockShape n) (r : Fin B.length → ℝ) {m : ℕ}
    (q : Fin B.length → Fin m) (t : Fin m → ℝ) (i : Fin B.length) : ℝ :=
  r i - (B.size i : ℝ) * t (q i)

/-- The residuals sum to zero over each fibre. -/
theorem residual_fibre_sum (h : GLBlockConeNumericalConditions B C r q t)
    (j : Fin C.length) :
    ∑ i ∈ univ.filter (fun i => q i = j), residual B r q t i = 0 := by
  obtain ⟨-, -, hsize, -, hmean, -⟩ := h
  have hw : ∑ i ∈ univ.filter (fun i => q i = j), (B.size i : ℝ) * t (q i) =
      (C.size j : ℝ) * t j := by
    rw [hsize j, Nat.cast_sum, sum_mul]
    exact sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]
  simp only [residual, sum_sub_distrib, hmean j, hw, sub_self]

/-- The residuals sum to zero over the blocks whose labels satisfy any predicate. -/
theorem residual_sum_filter (h : GLBlockConeNumericalConditions B C r q t)
    (P : Fin C.length → Prop) [DecidablePred P] :
    ∑ i ∈ univ.filter (fun i => P (q i)), residual B r q t i = 0 := by
  rw [← sum_fiberwise (univ.filter fun i => P (q i)) q (residual B r q t)]
  refine sum_eq_zero fun j _ => ?_
  rw [filter_filter]
  by_cases hj : P j
  · have hset : univ.filter (fun i => P (q i) ∧ q i = j) = univ.filter (fun i => q i = j) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      rintro rfl
      exact hj
    rw [hset]
    exact residual_fibre_sum h j
  · have hset : univ.filter (fun i => P (q i) ∧ q i = j) = ∅ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      rintro hi rfl
      exact hj hi
    rw [hset, sum_empty]

/-- The residuals have zero total. -/
theorem residual_sum (h : GLBlockConeNumericalConditions B C r q t) :
    ∑ i, residual B r q t i = 0 := by
  rw [← sum_fiberwise univ q (residual B r q t)]
  exact sum_eq_zero fun j _ => residual_fibre_sum h j

/-- The residuals are orthogonal to the exponents of their own blocks. -/
theorem residual_mul_sum (h : GLBlockConeNumericalConditions B C r q t) :
    ∑ i, residual B r q t i * t (q i) = 0 := by
  rw [← sum_fiberwise univ q (fun i => residual B r q t i * t (q i))]
  refine sum_eq_zero fun j _ => ?_
  calc ∑ i ∈ univ.filter (fun i => q i = j), residual B r q t i * t (q i)
      = ∑ i ∈ univ.filter (fun i => q i = j), residual B r q t i * t j :=
        sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]
    _ = 0 := by rw [← sum_mul, residual_fibre_sum h j, zero_mul]

/-- The inclusive prefix sums of the residuals are nonpositive. -/
theorem residual_prefix (h : GLBlockConeNumericalConditions B C r q t)
    (i : Fin B.length) :
    ∑ k ∈ univ.filter (fun k => k ≤ i), residual B r q t k ≤ 0 := by
  have hmono : Monotone q := h.1
  have hres := h.2.2.2.2.2 i
  -- Earlier complete fibres, followed by the initial part of the fibre of `i`.
  have hset : univ.filter (fun k => k ≤ i) =
      univ.filter (fun k => q k < q i) ∪ univ.filter (fun k => q k = q i ∧ k ≤ i) := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro hk
      rcases (hmono hk).lt_or_eq with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, hk⟩
    · rintro (hlt | ⟨-, hk⟩)
      · exact (hmono.reflect_lt hlt).le
      · exact hk
  have hdisj : Disjoint (univ.filter (fun k => q k < q i))
      (univ.filter (fun k => q k = q i ∧ k ≤ i)) :=
    disjoint_filter.2 fun k _ hlt heq => hlt.ne heq.1
  rw [hset, sum_union hdisj, residual_sum_filter h (fun j => j < q i), zero_add]
  calc ∑ k ∈ univ.filter (fun k => q k = q i ∧ k ≤ i), residual B r q t k
      = ∑ k ∈ univ.filter (fun k => q k = q i ∧ k ≤ i),
          (r k - (B.size k : ℝ) * t (q i)) :=
        sum_congr rfl fun k hk => by rw [residual, (mem_filter.1 hk).2.1]
    _ ≤ 0 := hres

/-- The residuals pair nonpositively with every antitone vector. -/
theorem residual_mul_sum_nonpos (h : GLBlockConeNumericalConditions B C r q t)
    {v : Fin B.length → ℝ} (hv : Antitone v) :
    ∑ i, residual B r q t i * v i ≤ 0 :=
  sum_mul_nonpos_of_antitone _ v hv (residual_prefix h) (residual_sum h)

/-- The exponents pulled back to the fine blocks are antitone. -/
theorem antitone_exponent (h : GLBlockConeNumericalConditions B C r q t) :
    Antitone fun i => t (q i) :=
  h.2.2.2.1.antitone.comp_monotone h.1

end Witness

section Compare

variable {n : ℕ} {B C D : BlockShape n} {r : Fin B.length → ℝ}
  {q : Fin B.length → Fin C.length} {t : Fin C.length → ℝ}
  {q' : Fin B.length → Fin D.length} {t' : Fin D.length → ℝ}

/-- Two sets of witnesses give the same exponent on every fine block. -/
theorem exponent_eq (hC : GLBlockConeNumericalConditions B C r q t)
    (hD : GLBlockConeNumericalConditions B D r q' t') (i : Fin B.length) :
    t (q i) = t' (q' i) := by
  have h1 := residual_mul_sum_nonpos hC (antitone_exponent hD)
  have h2 := residual_mul_sum hC
  have h3 := residual_mul_sum_nonpos hD (antitone_exponent hC)
  have h4 := residual_mul_sum hD
  have hid : ∑ k, (B.size k : ℝ) * (t (q k) - t' (q' k)) ^ 2 =
      ((∑ k, residual B r q t k * t' (q' k)) - ∑ k, residual B r q t k * t (q k)) +
        ((∑ k, residual B r q' t' k * t (q k)) - ∑ k, residual B r q' t' k * t' (q' k)) := by
    rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun k _ => by simp only [residual]; ring
  have hnn : ∀ k ∈ (univ : Finset (Fin B.length)),
      0 ≤ (B.size k : ℝ) * (t (q k) - t' (q' k)) ^ 2 :=
    fun k _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hzero := (sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm (by linarith) (sum_nonneg hnn))
    i (mem_univ i)
  have hw : (0 : ℝ) < B.size i := by exact_mod_cast B.positive i
  have hsq : (t (q i) - t' (q' i)) ^ 2 = 0 := by
    rcases mul_eq_zero.1 hzero with h0 | h0
    · exact absurd h0 hw.ne'
    · exact h0
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq)

/-- Both labellings induce the same order on the fine blocks. -/
theorem label_le_iff (hC : GLBlockConeNumericalConditions B C r q t)
    (hD : GLBlockConeNumericalConditions B D r q' t') (i k : Fin B.length) :
    q i ≤ q k ↔ q' i ≤ q' k := by
  have hanti : StrictAnti t := hC.2.2.2.1
  have hanti' : StrictAnti t' := hD.2.2.2.1
  rw [← hanti.le_iff_ge, ← hanti'.le_iff_ge, exponent_eq hC hD, exponent_eq hC hD]

end Compare

/-- Surjective labellings inducing the same order agree up to the cast of their lengths. -/
theorem labels_eq {m m' : ℕ} (q : Fin L → Fin m) (q' : Fin L → Fin m')
    (hq : Function.Surjective q) (hq' : Function.Surjective q')
    (hiff : ∀ i k, q i ≤ q k ↔ q' i ≤ q' k) :
    ∃ h : m = m', ∀ i, q' i = Fin.cast h (q i) := by
  let φ : Fin m → Fin m' := fun j => q' (Function.surjInv hq j)
  have hφ : ∀ i, φ (q i) = q' i := by
    intro i
    have hs : q (Function.surjInv hq (q i)) = q i := Function.surjInv_eq hq (q i)
    exact le_antisymm ((hiff _ _).1 hs.le) ((hiff _ _).1 hs.ge)
  have hφmono : StrictMono φ := by
    intro j j' hjj'
    have hs := Function.surjInv_eq hq j
    have hs' := Function.surjInv_eq hq j'
    refine lt_of_not_ge fun hle => ?_
    have := (hiff _ _).2 hle
    rw [hs, hs'] at this
    exact absurd hjj' (not_lt_of_ge this)
  have hφsurj : Function.Surjective φ := fun j' => by
    obtain ⟨i, rfl⟩ := hq' j'
    exact ⟨q i, hφ i⟩
  have hlen : m = m' := by
    simpa using Fintype.card_of_bijective ⟨hφmono.injective, hφsurj⟩
  subst hlen
  have hid : φ = id :=
    (hφmono.range_inj_of_wellFoundedLT strictMono_id).1
      (by rw [hφsurj.range_eq, Set.range_id])
  refine ⟨rfl, fun i => ?_⟩
  rw [← hφ i, hid]
  rfl

end ParabolicConeUniqueness

open ParabolicConeUniqueness in
/-- The numerical cone conditions determine the actual ordered coarse block shape. -/
theorem glBlockConeUnique : GLBlockConeUniquenessStatement := by
  intro n B r C D q t q' t' hC hD
  obtain ⟨hl, hqq'⟩ := labels_eq q q' hC.2.1 hD.2.1 (label_le_iff hC hD)
  refine BlockShape.ext_of_size hl fun j => ?_
  rw [hC.2.2.1 j, hD.2.2.1 (Fin.cast hl j)]
  refine sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_filter, mem_univ, true_and, hqq' i, Fin.cast_inj]

end Langlands

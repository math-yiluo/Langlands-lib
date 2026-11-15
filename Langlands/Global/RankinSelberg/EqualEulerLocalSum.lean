import Langlands.Representation.RankinSelberg.SchurCauchyEvaluation
import Langlands.Representation.RankinSelberg.SymmetricDominant
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Global.Factors.CuspidalPairFiniteLayer

/-! # The local unramified sum of the equal-rank Whittaker integral

The Cauchy identity summed over the dominant weights with nonnegative last coordinate,
with an explicit radius that is uniform in the residue cardinality, the identification
of the sum with the unramified pair Euler factor, and the cancellation of the modulus
character against the two spherical Whittaker values. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Global.RankinSelbergGlobal.EqualEulerLocal

open Langlands.GeneralLinear.Spherical

/-- An explicit rate controlling the pair Schur terms of `a` and `b`:
`(1 + ∑ ‖a_i‖) ^ (n + 1) * (1 + ∑ ‖b_j‖) ^ (n + 1)`. -/
def pairGrowth {n : ℕ} (a b : Fin (n + 1) → ℂˣ) : ℝ :=
  completeGrowthRate (fun i => (a i : ℂ)) ^ (n + 1) *
    completeGrowthRate (fun i => (b i : ℂ)) ^ (n + 1)

theorem norm_jacobiTrudiValue_le_rate {m : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]
    (x : σ → ℂ) (α : Fin m → ℕ) :
    ‖jacobiTrudiValue x α‖ ≤
      ((Fintype.card (Equiv.Perm (Fin m)) : ℝ) * completeGrowthConstant x ^ m *
          (completeGrowthRate x ^ m) ^ m) *
        (completeGrowthRate x ^ m) ^ (∑ i, α i) := by
  refine (norm_jacobiTrudiValue_le x α).trans_eq ?_
  have hpow : (completeGrowthRate x ^ (∑ i, α i)) ^ m =
      (completeGrowthRate x ^ m) ^ (∑ i, α i) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  simp only [pow_add, mul_pow]
  rw [hpow]
  ring

theorem norm_le_completeGrowthRate_pow {n : ℕ} (x : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    ‖x i‖ ≤ completeGrowthRate x ^ (n + 1) := by
  have hi : ‖x i‖ ≤ ∑ j, ‖x j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ i)
  have h1 : ‖x i‖ ≤ completeGrowthRate x := by
    unfold completeGrowthRate
    linarith
  exact h1.trans (le_self_pow₀ (completeGrowthRate_ge_one x) (Nat.succ_ne_zero n))

/-- The partition-indexed Cauchy series converges absolutely, with the Euler product as
its sum, as soon as `pairGrowth a b * ‖t‖ < 1`. -/
theorem summable_and_tsum_schurPairTerm {n : ℕ} (a b : Fin (n + 1) → ℂˣ) (t : ℂ)
    (ht : pairGrowth a b * ‖t‖ < 1) :
    Summable (fun α : {α : Fin (n + 1) → ℕ // Antitone α} =>
        ‖schurPairTerm (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) t α.val‖) ∧
      (∑' α : {α : Fin (n + 1) → ℕ // Antitone α},
          schurPairTerm (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) t α.val) =
        (∏ i : Fin (n + 1), ∏ j : Fin (n + 1), (1 - (a i : ℂ) * b j * t))⁻¹ := by
  set x : Fin (n + 1) → ℂ := fun i => (a i : ℂ)
  set y : Fin (n + 1) → ℂ := fun j => (b j : ℂ)
  have hAx := one_le_pow₀ (n := n + 1) (completeGrowthRate_ge_one x)
  have hAy := one_le_pow₀ (n := n + 1) (completeGrowthRate_ge_one y)
  have hCx : 0 < (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) *
      completeGrowthConstant x ^ (n + 1) * (completeGrowthRate x ^ (n + 1)) ^ (n + 1) := by
    have := completeGrowthConstant_pos x
    have := completeGrowthRate_pos x
    have : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (n + 1))) := by
      exact_mod_cast Fintype.card_pos
    positivity
  have hCy : 0 < (Fintype.card (Equiv.Perm (Fin (n + 1))) : ℝ) *
      completeGrowthConstant y ^ (n + 1) * (completeGrowthRate y ^ (n + 1)) ^ (n + 1) := by
    have := completeGrowthConstant_pos y
    have := completeGrowthRate_pos y
    have : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (n + 1))) := by
      exact_mod_cast Fintype.card_pos
    positivity
  have hall := summable_norm_schurPairTerm_of_bounds (m := n + 1) x y _ _ _ _ hCx hAx hCy hAy
    (norm_jacobiTrudiValue_le_rate x) (norm_jacobiTrudiValue_le_rate y) t ht
  have hsum : Summable (fun α : {α : Fin (n + 1) → ℕ // Antitone α} =>
      ‖schurPairTerm x y t α.val‖) := hall.subtype _
  refine ⟨hsum, ?_⟩
  rw [tsum_schurPairTerm_eq_seriesValue x y t hsum]
  have hxy : ∀ i j, ‖x i * y j * t‖ < 1 := by
    intro i j
    rw [norm_mul, norm_mul]
    refine lt_of_le_of_lt ?_ ht
    unfold pairGrowth
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (norm_le_completeGrowthRate_pow x i) (norm_le_completeGrowthRate_pow y j)
        (norm_nonneg _) (le_trans zero_le_one hAx))
      (norm_nonneg t)
  rw [seriesValue_complexCauchySeries x y t hxy, Finset.prod_comm]

/-- The integral weight attached to a natural weight. -/
def natWeight {n : ℕ} (α : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ := fun i => (α i : ℤ)

theorem natWeight_injective {n : ℕ} : Function.Injective (natWeight (n := n)) := by
  intro α β h
  funext i
  have := congrFun h i
  simp only [natWeight] at this
  exact_mod_cast this

/-- The equal-rank local term at a weight `lam`: on dominant weights with `lam_n ≥ 0`
it is `s_lam(a) s_lam(b) t ^ |lam|`, and it vanishes on all other weights. -/
def equalRankLocalTerm {n : ℕ} (a b : Fin (n + 1) → ℂˣ) (t : ℂ) (lam : Fin (n + 1) → ℤ) :
    ℂ :=
  if Antitone lam ∧ 0 ≤ lam (Fin.last n) then
    satakeSchur a lam * satakeSchur b lam * t ^ (∑ i, lam i).toNat
  else 0

theorem equalRankLocalTerm_natWeight {n : ℕ} (a b : Fin (n + 1) → ℂˣ) (t : ℂ)
    (α : {α : Fin (n + 1) → ℕ // Antitone α}) :
    equalRankLocalTerm a b t (natWeight α.val) =
      schurPairTerm (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) t α.val := by
  have hanti : Antitone (natWeight α.val) := fun i j hij => by
    simp only [natWeight]
    exact_mod_cast α.property hij
  have hpos : ∀ i, 0 ≤ natWeight α.val i := fun i => Int.natCast_nonneg _
  have hcond : Antitone (natWeight α.val) ∧ 0 ≤ natWeight α.val (Fin.last n) :=
    ⟨hanti, hpos _⟩
  simp only [equalRankLocalTerm, hcond, and_self, ↓reduceIte]
  rw [satakeSchur_eq_eval_jacobiTrudi a _ hanti hpos,
    satakeSchur_eq_eval_jacobiTrudi b _ hanti hpos]
  have hsum : (∑ i, natWeight α.val i).toNat = ∑ i, α.val i := by
    simp only [natWeight]
    rw [← Nat.cast_sum, Int.toNat_natCast]
  rw [hsum]
  rfl

theorem equalRankLocalTerm_eq_zero {n : ℕ} (a b : Fin (n + 1) → ℂˣ) (t : ℂ)
    (lam : Fin (n + 1) → ℤ)
    (hlam : lam ∉ Set.range (fun α : {α : Fin (n + 1) → ℕ // Antitone α} => natWeight α.val)) :
    equalRankLocalTerm a b t lam = 0 := by
  unfold equalRankLocalTerm
  split_ifs with hcond
  · exfalso
    obtain ⟨hanti, hlast⟩ := hcond
    apply hlam
    have hpos : ∀ i, 0 ≤ lam i := fun i => hlast.trans (hanti (Fin.le_last i))
    refine ⟨⟨fun i => (lam i).toNat, fun i j hij => Int.toNat_le_toNat (hanti hij)⟩, ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hpos i)
  · rfl

/-- **Local equal-rank unramified sum.** If `pairGrowth a b * ‖t‖ < 1`, then
`∑_lam s_lam(a) s_lam(b) t ^ |lam|`, over the dominant integral weights `lam` with
`lam_n ≥ 0`, converges absolutely to `∏_(i,j) (1 - a_i b_j t)⁻¹`. -/
theorem hasSum_equalRankLocalTerm {n : ℕ} (a b : Fin (n + 1) → ℂˣ) (t : ℂ)
    (ht : pairGrowth a b * ‖t‖ < 1) :
    HasSum (equalRankLocalTerm a b t)
      (∏ i : Fin (n + 1), ∏ j : Fin (n + 1), (1 - (a i : ℂ) * b j * t))⁻¹ := by
  obtain ⟨hsum, hval⟩ := summable_and_tsum_schurPairTerm a b t ht
  have hinj : Function.Injective
      (fun α : {α : Fin (n + 1) → ℕ // Antitone α} => natWeight α.val) :=
    natWeight_injective.comp Subtype.val_injective
  rw [← hinj.hasSum_iff (equalRankLocalTerm_eq_zero a b t)]
  have hfun : (equalRankLocalTerm a b t ∘
      fun α : {α : Fin (n + 1) → ℕ // Antitone α} => natWeight α.val) =
      fun α => schurPairTerm (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) t α.val := by
    funext α
    exact equalRankLocalTerm_natWeight a b t α
  rw [hfun, ← hval]
  exact hsum.of_norm.hasSum

/-- The absolute version of `hasSum_equalRankLocalTerm`. -/
theorem summable_norm_equalRankLocalTerm {n : ℕ} (a b : Fin (n + 1) → ℂˣ) (t : ℂ)
    (ht : pairGrowth a b * ‖t‖ < 1) :
    Summable (fun lam => ‖equalRankLocalTerm a b t lam‖) := by
  obtain ⟨hsum, -⟩ := summable_and_tsum_schurPairTerm a b t ht
  have hinj : Function.Injective
      (fun α : {α : Fin (n + 1) → ℕ // Antitone α} => natWeight α.val) :=
    natWeight_injective.comp Subtype.val_injective
  have hz : ∀ lam ∉ Set.range
      (fun α : {α : Fin (n + 1) → ℕ // Antitone α} => natWeight α.val),
      ‖equalRankLocalTerm a b t lam‖ = 0 := fun lam hlam => by
    rw [equalRankLocalTerm_eq_zero a b t lam hlam, norm_zero]
  rw [← hinj.summable_iff hz]
  have hfun : ((fun lam => ‖equalRankLocalTerm a b t lam‖) ∘
      fun α : {α : Fin (n + 1) → ℕ // Antitone α} => natWeight α.val) =
      fun α => ‖schurPairTerm (fun i => (a i : ℂ)) (fun j => (b j : ℂ)) t α.val‖ := by
    funext α
    exact congrArg norm (equalRankLocalTerm_natWeight a b t α)
  rw [hfun]
  exact hsum

/-! ### A radius uniform in the residue cardinality -/

/-- The exponent `(n + 1) (2 (n + 1) + C⁺ + C'⁺)` of the uniform radius for Satake
parameters bounded by `q ^ C` and `q ^ C'`. -/
def localRadius (n : ℕ) (C C' : ℝ) : ℝ :=
  ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + max C 0 + max C' 0)

theorem succ_succ_le_two_pow (n : ℕ) : n + 2 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

theorem completeGrowthRate_le_rpow {n : ℕ} (x : Fin (n + 1) → ℂ) {q C : ℝ} (hq : 2 ≤ q)
    (hx : ∀ i, ‖x i‖ ≤ q ^ C) : completeGrowthRate x ≤ q ^ (((n : ℝ) + 1) + max C 0) := by
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hC : ∀ i, ‖x i‖ ≤ q ^ max C 0 := fun i =>
    (hx i).trans (Real.rpow_le_rpow_of_exponent_le hq1 (le_max_left _ _))
  have h1 : 1 ≤ q ^ max C 0 := Real.one_le_rpow hq1 (le_max_right _ _)
  have hsum : ∑ i, ‖x i‖ ≤ ((n : ℝ) + 1) * q ^ max C 0 := by
    calc ∑ i, ‖x i‖ ≤ ∑ _i : Fin (n + 1), q ^ max C 0 := Finset.sum_le_sum fun i _ => hC i
      _ = ((n : ℝ) + 1) * q ^ max C 0 := by simp
  have hnat : n + 2 ≤ 2 ^ (n + 1) := succ_succ_le_two_pow n
  have h2 : (n : ℝ) + 2 ≤ q ^ ((n : ℝ) + 1) := by
    calc (n : ℝ) + 2 = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ (n + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (2 : ℝ) ^ (n + 1) := by push_cast; ring
      _ ≤ q ^ (n + 1) := pow_le_pow_left₀ (by norm_num) hq _
      _ = q ^ ((n : ℝ) + 1) := by rw [← Real.rpow_natCast]; push_cast; ring_nf
  unfold completeGrowthRate
  rw [Real.rpow_add hq0]
  calc 1 + ∑ i, ‖x i‖ ≤ 1 + ((n : ℝ) + 1) * q ^ max C 0 := by linarith
    _ ≤ ((n : ℝ) + 2) * q ^ max C 0 := by nlinarith
    _ ≤ q ^ ((n : ℝ) + 1) * q ^ max C 0 := mul_le_mul_of_nonneg_right h2 (by positivity)

/-- If every `‖a_i‖ ≤ q ^ C` and every `‖b_j‖ ≤ q ^ C'` with `q ≥ 2`, then
`pairGrowth a b ≤ q ^ localRadius n C C'`. -/
theorem pairGrowth_le_rpow {n : ℕ} (a b : Fin (n + 1) → ℂˣ) {q C C' : ℝ} (hq : 2 ≤ q)
    (ha : ∀ i, ‖(a i : ℂ)‖ ≤ q ^ C) (hb : ∀ j, ‖(b j : ℂ)‖ ≤ q ^ C') :
    pairGrowth a b ≤ q ^ localRadius n C C' := by
  have hq0 : 0 < q := by linarith
  have h1 := completeGrowthRate_le_rpow (fun i => (a i : ℂ)) hq ha
  have h2 := completeGrowthRate_le_rpow (fun j => (b j : ℂ)) hq hb
  have e : ∀ D : ℝ, (q ^ (((n : ℝ) + 1) + D)) ^ (n + 1) =
      q ^ (((n : ℝ) + 1) * (((n : ℝ) + 1) + D)) := by
    intro D
    rw [← Real.rpow_mul_natCast hq0.le]
    congr 1
    push_cast
    ring
  unfold pairGrowth localRadius
  calc _ ≤ (q ^ (((n : ℝ) + 1) + max C 0)) ^ (n + 1) *
        (q ^ (((n : ℝ) + 1) + max C' 0)) ^ (n + 1) :=
        mul_le_mul (pow_le_pow_left₀ (completeGrowthRate_pos _).le h1 _)
          (pow_le_pow_left₀ (completeGrowthRate_pos _).le h2 _)
          (pow_nonneg (completeGrowthRate_pos _).le _) (by positivity)
    _ = q ^ (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + max C 0 + max C' 0)) := by
        rw [e, e, ← Real.rpow_add hq0]
        congr 1
        ring

/-- **Uniform radius.** For a residue cardinality `q ≥ 2` and Satake parameters bounded by
`q ^ C` and `q ^ C'`, the hypothesis of `hasSum_equalRankLocalTerm` holds at
`t = q ^ (-s)` as soon as `localRadius n C C' < Re s`. The bound does not depend on `q`. -/
theorem pairGrowth_mul_norm_spectralPoint_lt {n : ℕ} (a b : Fin (n + 1) → ℂˣ) {q : ℕ}
    (hq : 2 ≤ q) {C C' : ℝ} (ha : ∀ i, ‖(a i : ℂ)‖ ≤ (q : ℝ) ^ C)
    (hb : ∀ j, ‖(b j : ℂ)‖ ≤ (q : ℝ) ^ C') {s : ℂ} (hs : localRadius n C C' < s.re) :
    pairGrowth a b * ‖RankinSelberg.spectralPoint q s‖ < 1 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  rw [RankinSelberg.spectralPoint, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  calc pairGrowth a b * (q : ℝ) ^ (-s.re) ≤
        (q : ℝ) ^ localRadius n C C' * (q : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (pairGrowth_le_rpow a b hq2 ha hb) (by positivity)
    _ = (q : ℝ) ^ (localRadius n C C' - s.re) := by
        rw [← Real.rpow_add hq0]
        ring_nf
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)

/-! ### The unramified pair Euler factor -/

theorem mem_ofTuple {n : ℕ} (a : Fin n → ℂˣ) (i : Fin n) :
    a i ∈ ((Unramified.Eigenvalues.ofTuple a : Unramified.Eigenvalues n) : Multiset ℂˣ) := by
  change a i ∈ ((List.ofFn a : List ℂˣ) : Multiset ℂˣ)
  rw [Multiset.mem_coe, List.mem_ofFn]
  exact ⟨i, rfl⟩

theorem eval_pairEulerPolynomial_ofTuple {n m : ℕ} (a : Fin n → ℂˣ) (b : Fin m → ℂˣ)
    (t : ℂ) :
    (CuspidalPairFunctionalEquation.pairEulerPolynomial (Unramified.Eigenvalues.ofTuple a)
        (Unramified.Eigenvalues.ofTuple b)).eval t =
      ∏ i, ∏ j, (1 - (a i : ℂ) * b j * t) := by
  rw [CuspidalPairFunctionalEquation.pairEulerPolynomial_ofTuple]
  simp [Polynomial.eval_prod]

/-- **Local equal-rank sum as the pair Euler factor.** Let `A`, `B` be Satake spectra of
rank `n + 1`, enumerated by `a`, `b`, whose elements are bounded by `q ^ C` and `q ^ C'`,
with `q ≥ 2`. For `localRadius n C C' < Re s` the local terms at `t = q ^ (-s)` sum to
`L(s) = (P_(A,B)(q ^ (-s)))⁻¹`, where `P_(A,B)` is the pair Euler polynomial. -/
theorem hasSum_equalRankLocalTerm_eulerFactor {n : ℕ} {A B : Unramified.Eigenvalues (n + 1)}
    (a b : Fin (n + 1) → ℂˣ) (hA : Unramified.Eigenvalues.ofTuple a = A)
    (hB : Unramified.Eigenvalues.ofTuple b = B) {q : ℕ} (hq : 2 ≤ q) {C C' : ℝ}
    (hCA : ∀ α ∈ (A : Multiset ℂˣ), ‖(α : ℂ)‖ ≤ (q : ℝ) ^ C)
    (hCB : ∀ β ∈ (B : Multiset ℂˣ), ‖(β : ℂ)‖ ≤ (q : ℝ) ^ C') {s : ℂ}
    (hs : localRadius n C C' < s.re) :
    HasSum (equalRankLocalTerm a b (RankinSelberg.spectralPoint q s))
      ((CuspidalPairFunctionalEquation.pairEulerPolynomial A B).eval
        (RankinSelberg.spectralPoint q s))⁻¹ := by
  subst hA hB
  rw [eval_pairEulerPolynomial_ofTuple]
  refine hasSum_equalRankLocalTerm a b _ (pairGrowth_mul_norm_spectralPoint_lt a b hq
    (fun i => hCA _ (mem_ofTuple a i)) (fun j => hCB _ (mem_ofTuple b j)) hs)

/-! ### The modulus character against the spherical Whittaker values -/

/-- `∑_(i<j) (lam_i - lam_j) = ∑_i (n - 2 i) lam_i`: the exponent of `δ_B⁻¹(ϖ ^ lam)`. -/
theorem sum_sub_of_lt_eq {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    (∑ i, ∑ j, if i < j then lam i - lam j else 0) =
      ∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i := by
  have hsplit : ∀ i j : Fin (n + 1), (if i < j then lam i - lam j else 0) =
      (if i < j then lam i else 0) - (if i < j then lam j else 0) := by
    intro i j
    split_ifs <;> simp
  simp only [hsplit, Finset.sum_sub_distrib]
  have h1 : ∀ i : Fin (n + 1), (∑ j, if i < j then lam i else 0) = ((n : ℤ) - i) * lam i := by
    intro i
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    push_cast [Nat.add_sub_cancel, hi]
    ring
  have h2 : ∀ j : Fin (n + 1), (∑ i, if i < j then lam j else 0) = (j : ℤ) * lam j := by
    intro j
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm (f := fun i j =>
    if i < j then lam j else 0), Finset.sum_congr rfl fun j _ => h2 j, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem halfModulus_mul_self (q : ℕ) {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    halfModulus q lam * halfModulus q lam =
      (q : ℂ) ^ (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i) := by
  unfold halfModulus
  rw [← mul_zpow, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg q),
    Complex.ofReal_natCast]

/-- `δ_B⁻¹(ϖ ^ lam) · (δ_B ^ (1/2)(ϖ ^ lam)) ^ 2 = 1`. -/
theorem zpow_mul_halfModulus_mul_self {q : ℕ} (hq : 0 < q) {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    (q : ℂ) ^ (∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i) *
      (halfModulus q lam * halfModulus q lam) = 1 := by
  rw [halfModulus_mul_self, zpow_neg,
    mul_inv_cancel₀ (zpow_ne_zero _ (by exact_mod_cast hq.ne'))]

/-- **The torus term.** The modulus weight `δ_B⁻¹(ϖ ^ lam)` times the torus values
`W°_a(ϖ ^ lam)`, `W°_b(ϖ ^ lam)` (as given by `sphericalWhittaker_torus`), the indicator of
`lam_n ≥ 0` and `t ^ |lam|` is the equal-rank local term. -/
theorem torusTerm_eq_equalRankLocalTerm {q : ℕ} (hq : 0 < q) {n : ℕ} (a b : Fin (n + 1) → ℂˣ)
    (t : ℂ) (lam : Fin (n + 1) → ℤ) :
    (q : ℂ) ^ (∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i) *
        ((if Antitone lam then halfModulus q lam * satakeSchur a lam else 0) *
          (if Antitone lam then halfModulus q lam * satakeSchur b lam else 0) *
          (if 0 ≤ lam (Fin.last n) then t ^ (∑ i, lam i).toNat else 0)) =
      equalRankLocalTerm a b t lam := by
  unfold equalRankLocalTerm
  by_cases h1 : Antitone lam <;> by_cases h2 : 0 ≤ lam (Fin.last n) <;>
    simp only [h1, h2, and_self, and_false, false_and, ↓reduceIte, mul_zero, zero_mul]
  calc _ = ((q : ℂ) ^ (∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i) *
        (halfModulus q lam * halfModulus q lam)) *
        (satakeSchur a lam * satakeSchur b lam * t ^ (∑ i, lam i).toNat) := by ring
    _ = _ := by rw [zpow_mul_halfModulus_mul_self hq, one_mul]

/-- The factor `|det ϖ ^ lam|_v ^ s` written as in `detPower`: if the norm is `q ^ (-k)`,
then `exp (s log q ^ (-k)) = (q ^ (-s)) ^ k`. -/
theorem exp_mul_log_zpow_eq_spectralPoint_pow {q : ℕ} (hq : 0 < q) (s : ℂ) (k : ℕ) :
    Complex.exp (s * (Real.log ((q : ℝ) ^ (-(k : ℤ))) : ℂ)) =
      RankinSelberg.spectralPoint q s ^ k := by
  rw [Real.log_zpow, RankinSelberg.spectralPoint,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hq.ne'), ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end Langlands.Global.RankinSelbergGlobal.EqualEulerLocal

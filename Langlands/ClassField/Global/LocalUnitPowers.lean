import Langlands.ClassField.Global.LocalUnitCohomology
import Langlands.Global.CompletionResidueAdic
import Langlands.Global.IntegralFiniteAdeles
import Mathlib.RingTheory.Henselian

/-! # Powers of local units have finite index -/

noncomputable section

universe u

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial IsLocalRing
open scoped NumberField Ring

section Hensel

/-- Hensel's lemma in an `I`-adically complete ring, without a monicity hypothesis: a simple
root modulo `I` lifts to a root. The proof is Mathlib's proof of
`IsAdicComplete.henselianRing`, which does not use monicity. -/
theorem exists_isRoot_of_isAdicComplete {R : Type*} [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f
  -- we define a sequence `c n` by starting at `a₀` and then continually
  -- applying the function sending `b` to `b - f(b)/f'(b)` (Newton's method).
  -- Note that `f'.eval b` is a unit, because `b` has the same residue as `a₀` modulo `I`.
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  -- we now spend some time determining properties of the sequence `c : ℕ → R`
  -- `hc_mod`: for every `n`, we have `c n ≡ a₀ [SMOD I]`
  -- `hf'c`  : for every `n`, `f'.eval (c n)` is a unit
  -- `hfcI`  : for every `n`, `f.eval (c n)` is contained in `I ^ (n+1)`
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => ?_
    rw [hc, sub_eq_add_neg, ← add_zero a₀]
    refine ih.add ?_
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine I.mul_mem_right _ ?_
    rw [← SModEq.zero] at h₁ ⊢
    exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    have := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih => ?_
    rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
      add_neg_cancel_comm]
    rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
    swap
    · intro i
      rw [zero_mul]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
        taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
        mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
      exact Ideal.zero_mem _
    · refine Submodule.sum_mem _ ?_
      simp only [Finset.mem_Ico]
      rintro i ⟨h2i, _⟩
      have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  -- we are now in the position to show that `c : ℕ → R` is a Cauchy sequence
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih => ?_
    rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
    refine ih.add ?_
    symm
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
    rw [add_assoc]
    exact le_self_add
  -- hence the sequence converges to some limit point `a`, which is the `a` we are looking for
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

/-- The binomial expansion of `(1 + d z) ^ d` with `d = e + 1`, with the factor `d ^ 2`
extracted from every term of positive degree. -/
theorem one_add_mul_pow_eq {R : Type*} [CommRing R] (e : ℕ) (z : R) :
    (1 + ((e + 1 : ℕ) : R) * z) ^ (e + 1) =
      1 + ((e + 1 : ℕ) : R) ^ 2 * (z + z ^ 2 * ∑ k ∈ Finset.range e,
        (((e + 1).choose (k + 2) : ℕ) : R) * ((e + 1 : ℕ) : R) ^ k * z ^ k) := by
  rw [add_comm (1 : R), add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  have key : ∑ k ∈ Finset.range e, (((e + 1 : ℕ) : R) * z) ^ (k + 1 + 1) *
      1 ^ (e + 1 - (k + 1 + 1)) * (((e + 1).choose (k + 1 + 1) : ℕ) : R) =
      ((e + 1 : ℕ) : R) ^ 2 * (z ^ 2 * ∑ k ∈ Finset.range e,
        (((e + 1).choose (k + 2) : ℕ) : R) * ((e + 1 : ℕ) : R) ^ k * z ^ k) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one]
    ring
  simp only [zero_add, pow_one, pow_zero, Nat.choose_one_right, Nat.choose_zero_right,
    Nat.cast_one, one_pow, mul_one, Nat.sub_zero] at key ⊢
  linear_combination key

end Hensel

section Local

variable {K : Type u} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "O" => adicCompletionIntegers K v

theorem compactSpace_adicCompletionIntegers : CompactSpace (v.adicCompletionIntegers K) :=
  isCompact_iff_compactSpace.mp (Langlands.Global.isCompact_adicCompletionIntegers K v)

open scoped Pointwise in
/-- The completed integer ring is complete for its maximal-ideal-adic topology. -/
theorem isAdicComplete_adicCompletionIntegers :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by
  have := compactSpace_adicCompletionIntegers v
  exact
  { prec' := fun f hf => by
      let S n : Set (v.adicCompletionIntegers K) :=
        f n +ᵥ ((maximalIdeal (v.adicCompletionIntegers K) ^ n :
          Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K))
      have hS n : S (n + 1) ⊆ S n := by
        apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
        simpa [S] using (hf n.le_succ).symm
      have h n : IsClosed (S n) :=
        (IsNoetherianRing.isClosed_ideal (maximalIdeal (v.adicCompletionIntegers K) ^ n)).vadd
          (f n)
      obtain ⟨L, hL⟩ :=
        (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
          (by simp [S]) h
      refine ⟨L, fun n ↦ ?_⟩
      obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
      simpa [SModEq.sub_mem] using hy }

/-- Every element of `1 + d ^ 2 𝔪` in the completed integer ring is a `d`-th power. -/
theorem exists_pow_eq_one_add_sq_mul (d : ℕ) (hd : d ≠ 0) (t : v.adicCompletionIntegers K)
    (ht : t ∈ maximalIdeal (v.adicCompletionIntegers K)) :
    ∃ y : v.adicCompletionIntegers K, y ^ d = 1 + (d : v.adicCompletionIntegers K) ^ 2 * t := by
  have := isAdicComplete_adicCompletionIntegers v
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  let G : O[X] := ∑ k ∈ Finset.range e,
    C ((((e + 1).choose (k + 2) : ℕ) : O) * ((e + 1 : ℕ) : O) ^ k) * X ^ k
  let f : O[X] := X + X ^ 2 * G - C t
  have h₁ : f.eval 0 ∈ maximalIdeal O := by
    simp only [f, eval_sub, eval_add, eval_X, eval_mul, eval_pow, eval_C]
    rw [zero_add, zero_pow two_ne_zero, zero_mul, zero_sub]
    exact (maximalIdeal O).neg_mem ht
  have h₂ : IsUnit (Ideal.Quotient.mk (maximalIdeal O) (f.derivative.eval 0)) := by
    have : f.derivative.eval 0 = 1 := by
      simp [f, derivative_mul]
    rw [this, map_one]
    exact isUnit_one
  obtain ⟨z, hz, -⟩ := exists_isRoot_of_isAdicComplete (maximalIdeal O) f 0 h₁ h₂
  have hz' : z + z ^ 2 * G.eval z = t := by
    have := hz.eq_zero
    simp only [f, eval_sub, eval_add, eval_X, eval_mul, eval_pow, eval_C] at this
    exact sub_eq_zero.mp this
  refine ⟨1 + ((e + 1 : ℕ) : O) * z, ?_⟩
  rw [one_add_mul_pow_eq e z, ← hz']
  simp only [G, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

/-- Valuation units of `K_v` regarded as units of the completed integer ring. -/
def localUnitsToIntegerUnits : localUnits v →* (v.adicCompletionIntegers K)ˣ where
  toFun u :=
    { val := ⟨((u : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        (le_of_eq ((mem_localUnits_iff v _).mp u.2) :
          Valued.v ((u : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1)⟩
      inv := ⟨(((u : (v.adicCompletion K)ˣ)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K),
        (le_of_eq ((mem_localUnits_iff v _).mp (inv_mem u.2)) :
          Valued.v ((((u : (v.adicCompletion K)ˣ)⁻¹ : (v.adicCompletion K)ˣ)) :
            v.adicCompletion K) ≤ 1)⟩
      val_inv := Subtype.ext (Units.mul_inv _)
      inv_val := Subtype.ext (Units.inv_mul _) }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem coe_localUnitsToIntegerUnits (u : localUnits v) :
    (((localUnitsToIntegerUnits v u : (v.adicCompletionIntegers K)ˣ) :
      v.adicCompletionIntegers K) : v.adicCompletion K) =
      ((u : (v.adicCompletion K)ˣ) : v.adicCompletion K) := rfl

/-- The `d`-th powers of valuation units. -/
def localUnitPowers (d : ℕ) : Subgroup (localUnits v) :=
  (powMonoidHom d : localUnits v →* localUnits v).range

theorem mem_localUnitPowers_iff (d : ℕ) (u : localUnits v) :
    u ∈ localUnitPowers v d ↔ ∃ y : localUnits v, y ^ d = u :=
  Iff.rfl

/-- The `d`-th powers of valuation units have finite index in the valuation units. -/
theorem localUnitPowers_finiteIndex (d : ℕ) (hd : d ≠ 0) : (localUnitPowers v d).FiniteIndex := by
  let I : Ideal O := Ideal.span {((d : O)) ^ 2} * maximalIdeal O
  have hd0 : (d : O) ≠ 0 := by
    have hK : ((d : O) : v.adicCompletion K) ≠ 0 := by
      rw [show ((d : O) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) d by simp]
      exact (_root_.map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hd)
    intro h
    apply hK
    rw [h]
    rfl
  have hI : I ≠ ⊥ := by
    intro h
    rcases Ideal.mul_eq_bot.mp h with h | h
    · rw [Ideal.span_singleton_eq_bot] at h
      exact hd0 (pow_eq_zero_iff two_ne_zero |>.mp h)
    · exact IsDiscreteValuationRing.not_a_field O h
  have hfin : Finite (O ⧸ I) := by
    obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal O
      (IsPrincipalIdealRing.principal _) I hI
    exact IsLocalRing.finite_quotient_iff.mpr ⟨n, hn.ge⟩
  let ψ : localUnits v →* (O ⧸ I)ˣ :=
    (Units.map (Ideal.Quotient.mk I).toMonoidHom).comp (localUnitsToIntegerUnits v)
  have hker : ψ.ker ≤ localUnitPowers v d := by
    intro u hu
    have h1 : ((localUnitsToIntegerUnits v u : Oˣ) : O) - 1 ∈ I := by
      rw [← Ideal.Quotient.eq]
      have := congrArg Units.val (MonoidHom.mem_ker.mp hu)
      simpa [ψ] using this
    obtain ⟨t, ht, hdt⟩ := Ideal.mem_span_singleton_mul.mp h1
    obtain ⟨y, hy⟩ := exists_pow_eq_one_add_sq_mul v d hd t ht
    have hyu : y ^ d = ((localUnitsToIntegerUnits v u : Oˣ) : O) := by
      rw [hy, hdt]
      ring
    have hy0 : (y : v.adicCompletion K) ≠ 0 := by
      intro h0
      have := congrArg (fun x : O => (x : v.adicCompletion K)) hyu
      simp only [SubmonoidClass.coe_pow, h0, zero_pow hd, coe_localUnitsToIntegerUnits] at this
      exact (u : (v.adicCompletion K)ˣ).ne_zero this.symm
    have hyv : Valued.v (y : v.adicCompletion K) = 1 := by
      have hle : Valued.v (y : v.adicCompletion K) ≤ 1 := y.2
      have hpow : Valued.v (y : v.adicCompletion K) ^ d = 1 := by
        rw [← map_pow]
        have := congrArg (fun x : O => (x : v.adicCompletion K)) hyu
        simp only [SubmonoidClass.coe_pow, coe_localUnitsToIntegerUnits] at this
        rw [this]
        exact (mem_localUnits_iff v _).mp u.2
      rcases hle.lt_or_eq with hlt | heq
      · exact absurd hpow (pow_lt_one₀ zero_le hlt hd).ne
      · exact heq
    refine ⟨⟨Units.mk0 (y : v.adicCompletion K) hy0, (mem_localUnits_iff v _).mpr hyv⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    have := congrArg (fun x : O => (x : v.adicCompletion K)) hyu
    simp only [SubmonoidClass.coe_pow, coe_localUnitsToIntegerUnits] at this
    simpa [powMonoidHom] using this
  have : Finite ψ.range := inferInstance
  exact Subgroup.finiteIndex_of_le hker

end Local

section Infinite

variable {K : Type u} [Field K] (v : InfinitePlace K)

/-- The `d`-th powers of units of the completion at an infinite place. -/
def infiniteUnitPowers (d : ℕ) : Subgroup (v.Completion)ˣ :=
  (powMonoidHom d : (v.Completion)ˣ →* (v.Completion)ˣ).range

theorem mem_infiniteUnitPowers_iff (d : ℕ) (x : (v.Completion)ˣ) :
    x ∈ infiniteUnitPowers v d ↔ ∃ y : (v.Completion)ˣ, y ^ d = x :=
  Iff.rfl

theorem infiniteUnitPowers_one : infiniteUnitPowers v 1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ⟨x, pow_one x⟩

/-- At a real place, squares have finite index in the units of the completion. The proof shows
that the classes of `1` and `-1` cover the quotient; that bound is not part of the statement. -/
theorem infiniteUnitPowers_two_finiteIndex (hv : v.IsReal) :
    (infiniteUnitPowers v 2).FiniteIndex := by
  let φ := InfinitePlace.Completion.ringEquivRealOfIsReal hv
  have hsq : ∀ x : (v.Completion)ˣ, x ∈ infiniteUnitPowers v 2 ∨ -x ∈ infiniteUnitPowers v 2 := by
    intro x
    have hx : φ (x : v.Completion) ≠ 0 := by simp
    have key : ∀ y : (v.Completion)ˣ, 0 < φ (y : v.Completion) → y ∈ infiniteUnitPowers v 2 := by
      intro y hy
      have hs : φ.symm (Real.sqrt (φ (y : v.Completion))) ≠ 0 := by
        simp [Real.sqrt_ne_zero'.mpr hy]
      refine ⟨Units.mk0 _ hs, ?_⟩
      apply Units.ext
      apply φ.injective
      simp [powMonoidHom, Real.sq_sqrt hy.le]
    rcases hx.lt_or_gt with h | h
    · right
      apply key
      simpa using h
    · left
      exact key x h
  have : Finite ((v.Completion)ˣ ⧸ infiniteUnitPowers v 2) := by
    refine Finite.of_surjective (fun b : Bool =>
      if b then (QuotientGroup.mk 1 : (v.Completion)ˣ ⧸ infiniteUnitPowers v 2)
      else QuotientGroup.mk (-1)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rcases hsq x with h | h
      · refine ⟨true, ?_⟩
        simp only [ite_true]
        rw [QuotientGroup.eq]
        simpa using h
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [QuotientGroup.eq]
        simpa using h
  exact Subgroup.finiteIndex_of_finite_quotient

end Infinite

end Langlands.ClassField.Global

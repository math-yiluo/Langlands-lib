import Langlands.GroupScheme.Unipotent.PrincipalPart
import Langlands.GroupScheme.Unipotent.OneDimensional.Additive

/-! # Additive curves in separated-variable polynomial kernels -/

noncomputable section

universe u v

open Polynomial
open scoped BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional

variable {k : Type u} [Field k] {ι : Type v}

theorem OneDimensional.IsAdditive.comp_add {f : k[X]} (hf : IsAdditive f)
    (a b : k[X]) : f.comp (a + b) = f.comp a + f.comp b := by
  exact hf.aeval_add a b

theorem OneDimensional.IsAdditive.comp_sub {f : k[X]} (hf : IsAdditive f)
    (a b : k[X]) : f.comp (a - b) = f.comp a - f.comp b := by
  have h := hf.comp_add (a - b) b
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem OneDimensional.IsAdditive.comp_zero {f : k[X]} (hf : IsAdditive f) :
    f.comp 0 = 0 := by
  exact hf.aeval_zero

theorem coeff_zero_comp_of_coeff_zero (f g : k[X])
    (hf : f.coeff 0 = 0) (hg : g.coeff 0 = 0) : (f.comp g).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_comp, ← coeff_zero_eq_eval_zero, hg,
    ← coeff_zero_eq_eval_zero, hf]

/-- A triangular polynomial change of coordinates with distinguished coordinate
`j`. Its `j`-th entry is supplied by `q j`; the other entries add `q i`. -/
def polynomialShear [DecidableEq ι] (j : ι) (q φ : ι → k[X]) : ι → k[X] :=
  fun i => (if i = j then 0 else φ i) + (q i).comp (φ j)

/-- The inverse formula when `q j = C a * X` and `a` is nonzero. -/
def polynomialShearInverse [DecidableEq ι] (j : ι) (a : k)
    (q φ : ι → k[X]) : ι → k[X] :=
  fun i => if i = j then C a⁻¹ * φ j else φ i - (q i).comp (C a⁻¹ * φ j)

theorem polynomialShear_inverse [DecidableEq ι] (j : ι) (a : k) (ha : a ≠ 0)
    (q φ : ι → k[X]) (hq : q j = C a * X) :
    polynomialShear j q (polynomialShearInverse j a q φ) = φ := by
  have hj : C a * (C a⁻¹ * φ j) = φ j := by
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
  funext i
  by_cases hi : i = j
  · subst i
    simpa [polynomialShear, polynomialShearInverse, hq] using hj
  · simp [polynomialShear, polynomialShearInverse, hi]

theorem polynomialShearInverse_shear [DecidableEq ι] (j : ι) (a : k) (ha : a ≠ 0)
    (q φ : ι → k[X]) (hq : q j = C a * X) :
    polynomialShearInverse j a q (polynomialShear j q φ) = φ := by
  have hj : C a⁻¹ * (C a * φ j) = φ j := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]
  funext i
  by_cases hi : i = j
  · subst i
    simpa [polynomialShear, polynomialShearInverse, hq] using hj
  · simp [polynomialShearInverse, polynomialShear, hi, hq, hj]

theorem polynomialShear_zero [DecidableEq ι] (j : ι) (q : ι → k[X])
    (hq : ∀ i, IsAdditive (q i)) : polynomialShear j q 0 = 0 := by
  funext i
  simp [polynomialShear, (hq i).comp_zero]

theorem polynomialShearInverse_zero [DecidableEq ι] (j : ι) (a : k) (q : ι → k[X])
    (hq : ∀ i, IsAdditive (q i)) : polynomialShearInverse j a q 0 = 0 := by
  funext i
  simp [polynomialShearInverse, (hq i).comp_zero]

theorem polynomialShear_isAdditive [DecidableEq ι] (j : ι) (q φ : ι → k[X])
    (hq : ∀ i, IsAdditive (q i)) (hφ : ∀ i, IsAdditive (φ i)) :
    ∀ i, IsAdditive (polynomialShear j q φ i) := by
  intro i
  apply IsAdditive.add
  · by_cases hi : i = j
    · simpa only [ite_eq_left hi] using (isAdditive_zero (k := k))
    · simpa only [ite_eq_right hi] using hφ i
  · exact (hq i).comp (hφ j)

theorem polynomialShear_coeff_zero [DecidableEq ι] (j : ι) (q φ : ι → k[X])
    (hq : ∀ i, (q i).coeff 0 = 0) (hφ : ∀ i, (φ i).coeff 0 = 0) :
    ∀ i, (polynomialShear j q φ i).coeff 0 = 0 := by
  intro i
  by_cases hi : i = j
  · subst i
    simp [polynomialShear, coeff_zero_comp_of_coeff_zero _ _ (hq j) (hφ j)]
  · simp [polynomialShear, hi, coeff_zero_comp_of_coeff_zero _ _ (hq i) (hφ j), hφ i]

theorem polynomialShearInverse_coeff_zero [DecidableEq ι] (j : ι) (a : k)
    (q φ : ι → k[X]) (hq : ∀ i, (q i).coeff 0 = 0)
    (hφ : ∀ i, (φ i).coeff 0 = 0) :
    ∀ i, (polynomialShearInverse j a q φ i).coeff 0 = 0 := by
  intro i
  by_cases hi : i = j
  · simp [polynomialShearInverse, hi, hφ]
  · have hpoint : (C a⁻¹ * φ j).coeff 0 = 0 := by simp [hφ]
    simp [polynomialShearInverse, hi, hφ,
      coeff_zero_comp_of_coeff_zero _ _ (hq i) hpoint]

theorem OneDimensional.IsAdditive.sum (s : Finset ι) (f : ι → k[X])
    (hf : ∀ i ∈ s, IsAdditive (f i)) : IsAdditive (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isAdditive_zero (k := k))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun l hl => hf l (Finset.mem_insert_of_mem hl))

variable [Fintype ι]

theorem sum_comp_polynomialShear [DecidableEq ι] (j : ι) (f q φ : ι → k[X])
    (hf : ∀ i, IsAdditive (f i)) :
    (∑ i, (f i).comp (polynomialShear j q φ i)) =
      ∑ i, (if i = j then ∑ l, (f l).comp (q l) else f i).comp (φ i) := by
  have hleft :
      (∑ i, (f i).comp (polynomialShear j q φ i)) =
        (∑ i, if i = j then 0 else (f i).comp (φ i)) +
          (∑ i, (f i).comp (q i)).comp (φ j) := by
    simp only [polynomialShear, (hf _).comp_add, ← Polynomial.comp_assoc,
      Polynomial.sum_comp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = j
    · simp [hi, (hf j).comp_zero]
    · simp [hi]
  rw [hleft]
  rw [← Finset.sum_erase_add (s := Finset.univ)
    (f := fun i => (if i = j then ∑ l, (f l).comp (q l) else f i).comp (φ i))
    (Finset.mem_univ j)]
  simp only [ite_true]
  congr 1
  rw [← Finset.sum_erase_add (s := Finset.univ)
    (f := fun i => if i = j then 0 else (f i).comp (φ i)) (Finset.mem_univ j)]
  simp only [ite_true, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp [(Finset.mem_erase.mp hi).1]

/-- A principal-part zero cancels the top term after a triangular additive
change of variables. -/
theorem natDegree_sum_comp_power_lt (p : ℕ) [ExpChar k p]
    (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i)) (m : ι → ℕ)
    (hm : ∀ i, (f i).natDegree = p ^ m i) (b : ι → k) (j : ι)
    (hmax : ∀ i, b i ≠ 0 → m i ≤ m j)
    (hb : (∑ i, (f i).leadingCoeff * b i ^ (f i).natDegree) = 0) :
    (∑ i, (f i).comp (C (b i) * X ^ p ^ (m j - m i))).natDegree <
      (f j).natDegree := by
  have hp : p ≠ 0 := expChar_ne_zero k p
  have hterm (i : ι) :
      ((f i).comp (C (b i) * X ^ p ^ (m j - m i))).natDegree ≤ p ^ m j ∧
      ((f i).comp (C (b i) * X ^ p ^ (m j - m i))).coeff (p ^ m j) =
        (f i).leadingCoeff * b i ^ (f i).natDegree := by
    by_cases hbi : b i = 0
    · have hdi : (f i).natDegree ≠ 0 := by
        rw [hm i]
        exact pow_ne_zero _ hp
      simp [hbi, (hf i).comp_zero, hdi]
    · have hqdeg : (C (b i) * X ^ p ^ (m j - m i)).natDegree =
          p ^ (m j - m i) := natDegree_C_mul_X_pow _ _ hbi
      have hpow : p ^ m i * p ^ (m j - m i) = p ^ m j := by
        rw [← pow_add, Nat.add_sub_of_le (hmax i hbi)]
      have hdeg : ((f i).comp (C (b i) * X ^ p ^ (m j - m i))).natDegree =
          p ^ m j := by
        rw [natDegree_comp, hm i, hqdeg, hpow]
      refine ⟨hdeg.le, ?_⟩
      rw [← hdeg, coeff_natDegree,
        leadingCoeff_comp (by rw [hqdeg]; exact pow_ne_zero _ hp),
        leadingCoeff_C_mul_X_pow]
  have hle : (∑ i, (f i).comp (C (b i) * X ^ p ^ (m j - m i))).natDegree ≤
      p ^ m j := natDegree_sum_le_of_forall_le _ _ fun i _ => (hterm i).1
  have hcoeff : (∑ i, (f i).comp (C (b i) * X ^ p ^ (m j - m i))).coeff
      (p ^ m j) = 0 := by
    rw [finsetSum_coeff]
    simpa only [(hterm _).2] using hb
  rw [hm j]
  apply lt_of_le_of_ne hle
  intro heq
  have hz : (∑ i, (f i).comp (C (b i) * X ^ p ^ (m j - m i))) = 0 := by
    apply leadingCoeff_eq_zero.mp
    rw [← coeff_natDegree, heq, hcoeff]
  rw [hz, natDegree_zero] at heq
  exact (pow_ne_zero (m j) hp) heq.symm

/-- Choose an additive shear whose substitution strictly decreases one
coordinate degree of an additive separated-variable equation. -/
theorem exists_degree_reducing_polynomialShear (p : ℕ) [ExpChar k p]
    (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i)) (hf0 : ∀ i, f i ≠ 0)
    (b : ι → k) (hb0 : b ≠ 0)
    (hb : (∑ i, (f i).leadingCoeff * b i ^ (f i).natDegree) = 0) :
    ∃ (j : ι) (a : k) (q : ι → k[X]), a ≠ 0 ∧ q j = C a * X ∧
      (∀ i, IsAdditive (q i)) ∧
      (∑ i, (f i).comp (q i)).natDegree < (f j).natDegree := by
  classical
  choose m hm using fun i => (hf i).natDegree_eq_pow p (hf0 i)
  let s := Finset.univ.filter fun i => b i ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
      by_contra hn
      apply hb0
      funext i
      simpa using (not_exists.mp hn i)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨j, hjs, hjmax⟩ := Finset.exists_mem_eq_sup s hs m
  have hmax (i : ι) (hi : b i ≠ 0) : m i ≤ m j := by
    rw [← hjmax]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  refine ⟨j, b j, fun i => C (b i) * X ^ p ^ (m j - m i),
    (Finset.mem_filter.mp hjs).2, ?_, ?_, ?_⟩
  · simp
  · intro i
    exact (isAdditive_X_pow p _).C_mul (b i)
  · exact natDegree_sum_comp_power_lt p f hf m hm b j hmax hb

private theorem exists_additive_kernel_curve_aux (p : ℕ) [ExpChar k p] :
    ∀ N : ℕ, ∀ f : ι → k[X], (∑ i, (f i).natDegree) ≤ N →
      (∀ i, IsAdditive (f i)) →
      ∀ φ : ι → k[X], (∀ i, (φ i).coeff 0 = 0) → φ ≠ 0 →
      (∑ i, (f i).comp (φ i)) = 0 →
      ∃ ψ : ι → k[X], ψ ≠ 0 ∧ (∀ i, IsAdditive (ψ i)) ∧
        (∑ i, (f i).comp (ψ i)) = 0 := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f hN hf φ hφ hφ0 hrel
    by_cases hf0 : ∀ i, f i ≠ 0
    · have hφpos : ∃ i, 0 < (φ i).natDegree := by
        by_contra hn
        apply hφ0
        funext i
        have hd : (φ i).natDegree = 0 := by
          have := not_exists.mp hn i
          omega
        rw [eq_C_of_natDegree_eq_zero hd, hφ i, C_0]
        rfl
      obtain ⟨b, hb0, hb⟩ := exists_principalPart_zero_of_sum_comp_eq_zero f φ
        (fun i => (hf i).coeff_zero) hφpos hrel
      obtain ⟨j, a, q, ha, hqj, hq, hlt⟩ :=
        exists_degree_reducing_polynomialShear p f hf hf0 b hb0 hb
      let g := ∑ i, (f i).comp (q i)
      let f' : ι → k[X] := fun i => if i = j then g else f i
      have hg : IsAdditive g := IsAdditive.sum _ _ fun i _ => (hf i).comp (hq i)
      have hf' : ∀ i, IsAdditive (f' i) := by
        intro i
        by_cases hi : i = j
        · simpa [f', hi] using hg
        · simpa [f', hi] using hf i
      have hsum : (∑ i, (f' i).natDegree) < ∑ i, (f i).natDegree := by
        apply Finset.sum_lt_sum
        · intro i _
          by_cases hi : i = j
          · simpa [f', hi] using hlt.le
          · simp [f', hi]
        · exact ⟨j, Finset.mem_univ j, by simpa [f', g] using hlt⟩
      let φ' := polynomialShearInverse j a q φ
      have hφ' : ∀ i, (φ' i).coeff 0 = 0 :=
        polynomialShearInverse_coeff_zero j a q φ (fun i => (hq i).coeff_zero) hφ
      have hφ'0 : φ' ≠ 0 := by
        intro hz
        have hinv : polynomialShear j q φ' = φ :=
          polynomialShear_inverse j a ha q φ hqj
        rw [hz, polynomialShear_zero j q hq] at hinv
        exact hφ0 hinv.symm
      have hrel' : (∑ i, (f' i).comp (φ' i)) = 0 := by
        change (∑ i, (if i = j then ∑ l, (f l).comp (q l) else f i).comp (φ' i)) = 0
        rw [← sum_comp_polynomialShear j f q φ' hf]
        change (∑ i, (f i).comp (polynomialShear j q
          (polynomialShearInverse j a q φ) i)) = 0
        rw [polynomialShear_inverse j a ha q φ hqj]
        exact hrel
      obtain ⟨ψ', hψ'0, hψ', hψ'rel⟩ := ih _ (hsum.trans_le hN) f' le_rfl hf' φ'
        hφ' hφ'0 hrel'
      refine ⟨polynomialShear j q ψ', ?_, polynomialShear_isAdditive j q ψ' hq hψ', ?_⟩
      · intro hz
        have hinv := polynomialShearInverse_shear j a ha q ψ' hqj
        rw [hz, polynomialShearInverse_zero j a q hq] at hinv
        exact hψ'0 hinv.symm
      · rw [sum_comp_polynomialShear j f q ψ' hf]
        exact hψ'rel
    · obtain ⟨j, hj⟩ : ∃ j, f j = 0 := by simpa using hf0
      let ψ : ι → k[X] := fun i => if i = j then X else 0
      refine ⟨ψ, ?_, ?_, ?_⟩
      · intro hz
        have hzj := congrFun hz j
        simp [ψ] at hzj
      · intro i
        by_cases hi : i = j
        · simpa [ψ, hi] using (isAdditive_X (k := k))
        · simpa [ψ, hi] using (isAdditive_zero (k := k))
      · apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i = j
        · simp [ψ, hi, hj]
        · simp [ψ, hi, (hf i).comp_zero]

/-- A nonzero pointed polynomial curve in an additive separated-variable kernel
can be replaced by a nonzero additive polynomial curve over the same field. -/
theorem exists_additive_kernel_curve_of_pointed (p : ℕ) [ExpChar k p]
    (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : ι → k[X]) (hφ : ∀ i, (φ i).coeff 0 = 0) (hφ0 : φ ≠ 0)
    (hrel : (∑ i, (f i).comp (φ i)) = 0) :
    ∃ ψ : ι → k[X], ψ ≠ 0 ∧ (∀ i, IsAdditive (ψ i)) ∧
      (∑ i, (f i).comp (ψ i)) = 0 :=
  exists_additive_kernel_curve_aux p _ f le_rfl hf φ hφ hφ0 hrel

/-- Any nonconstant polynomial curve in an additive separated-variable kernel
produces a nonzero additive polynomial curve, over every field. -/
theorem exists_additive_kernel_curve
    (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : ι → k[X]) (hφ : ∃ i, 0 < (φ i).natDegree)
    (hrel : (∑ i, (f i).comp (φ i)) = 0) :
    ∃ ψ : ι → k[X], ψ ≠ 0 ∧ (∀ i, IsAdditive (ψ i)) ∧
      (∑ i, (f i).comp (ψ i)) = 0 := by
  classical
  let φ' : ι → k[X] := fun i => φ i - C ((φ i).coeff 0)
  have hφ' : ∀ i, (φ' i).coeff 0 = 0 := by
    intro i
    simp [φ']
  have hφ'0 : φ' ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hφ
    have hzi : φ i = C ((φ i).coeff 0) := sub_eq_zero.mp (congrFun hz i)
    rw [hzi, natDegree_C] at hi
    omega
  have hconst : (∑ i, (f i).comp (C ((φ i).coeff 0))) = 0 := by
    calc
      _ = (∑ i, (f i).comp (φ i)).comp 0 := by
        rw [Polynomial.sum_comp]
        apply Finset.sum_congr rfl
        intro i _
        rw [Polynomial.comp_assoc, Polynomial.comp_zero, ← coeff_zero_eq_eval_zero]
      _ = 0 := by rw [hrel]; simp
  have hrel' : (∑ i, (f i).comp (φ' i)) = 0 := by
    change (∑ i, (f i).comp (φ i - C ((φ i).coeff 0))) = 0
    simp only [(hf _).comp_sub, Finset.sum_sub_distrib, hrel, hconst, sub_self]
  exact exists_additive_kernel_curve_of_pointed (ringExpChar k) f hf φ' hφ' hφ'0 hrel'

end Langlands.GroupScheme.Unipotent

import Langlands.GroupScheme.Unipotent.AdditiveKernelCurve

/-! # Split additive curves in separated-variable kernels -/

noncomputable section

universe u v w

open Polynomial
open scoped BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional

variable {k : Type u} [Field k] {ι : Type v}

/-- The coordinate polynomials that express an inverse triangular shear as
another triangular shear. -/
def polynomialShearInverseCoordinates [DecidableEq ι] (j : ι) (a : k)
    (q : ι → k[X]) : ι → k[X] :=
  fun i => if i = j then C a⁻¹ * X else -(q i).comp (C a⁻¹ * X)

theorem polynomialShearInverse_eq_shear [DecidableEq ι] (j : ι) (a : k)
    (q φ : ι → k[X]) :
    polynomialShearInverse j a q φ =
      polynomialShear j (polynomialShearInverseCoordinates j a q) φ := by
  funext i
  by_cases hi : i = j
  · simp [polynomialShearInverse, polynomialShear, polynomialShearInverseCoordinates, hi]
  · simp [polynomialShearInverse, polynomialShear, polynomialShearInverseCoordinates, hi,
      Polynomial.comp_assoc, sub_eq_add_neg]

theorem polynomialShearInverseCoordinates_isAdditive [DecidableEq ι] (j : ι) (a : k)
    (q : ι → k[X]) (hq : ∀ i, IsAdditive (q i)) :
    ∀ i, IsAdditive (polynomialShearInverseCoordinates j a q i) := by
  intro i
  by_cases hi : i = j
  · simpa [polynomialShearInverseCoordinates, hi] using
      (isAdditive_X (k := k)).C_mul a⁻¹
  · simpa [polynomialShearInverseCoordinates, hi] using
      ((hq i).comp ((isAdditive_X (k := k)).C_mul a⁻¹)).neg

variable [Fintype ι]

/-- A polynomial curve in an additive kernel admitting an additive polynomial
retraction from the ambient vector coordinates. -/
def HasSplitAdditiveKernelCurve (f : ι → k[X]) : Prop :=
  ∃ ψ r : ι → k[X], (∀ i, IsAdditive (ψ i)) ∧ (∀ i, IsAdditive (r i)) ∧
    (∑ i, (f i).comp (ψ i)) = 0 ∧ (∑ i, (r i).comp (ψ i)) = X

private theorem hasSplitAdditiveKernelCurve_aux (p : ℕ) [ExpChar k p] :
    ∀ N : ℕ, ∀ f : ι → k[X], (∑ i, (f i).natDegree) ≤ N →
      (∀ i, IsAdditive (f i)) →
      ∀ φ : ι → k[X], (∀ i, (φ i).coeff 0 = 0) → φ ≠ 0 →
      (∑ i, (f i).comp (φ i)) = 0 → HasSplitAdditiveKernelCurve f := by
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
      obtain ⟨ψ', r', hψ', hr', hψ'rel, hret'⟩ :=
        ih _ (hsum.trans_le hN) f' le_rfl hf' φ' hφ' hφ'0 hrel'
      let qinv := polynomialShearInverseCoordinates j a q
      have hqinv : ∀ i, IsAdditive (qinv i) :=
        polynomialShearInverseCoordinates_isAdditive j a q hq
      let r : ι → k[X] := fun i =>
        if i = j then ∑ l, (r' l).comp (qinv l) else r' i
      refine ⟨polynomialShear j q ψ', r, polynomialShear_isAdditive j q ψ' hq hψ',
        ?_, ?_, ?_⟩
      · intro i
        by_cases hi : i = j
        · simpa [r, hi] using
            (IsAdditive.sum Finset.univ _ fun l _ => (hr' l).comp (hqinv l))
        · simpa [r, hi] using hr' i
      · rw [sum_comp_polynomialShear j f q ψ' hf]
        exact hψ'rel
      · change (∑ i, (if i = j then ∑ l, (r' l).comp (qinv l) else r' i).comp
          (polynomialShear j q ψ' i)) = X
        rw [← sum_comp_polynomialShear j r' qinv (polynomialShear j q ψ') hr']
        change (∑ i, (r' i).comp (polynomialShear j
          (polynomialShearInverseCoordinates j a q) (polynomialShear j q ψ') i)) = X
        rw [← polynomialShearInverse_eq_shear j a q (polynomialShear j q ψ'),
          polynomialShearInverse_shear j a ha q ψ' hqj]
        exact hret'
    · obtain ⟨j, hj⟩ : ∃ j, f j = 0 := by simpa using hf0
      let ψ : ι → k[X] := fun i => if i = j then X else 0
      have hψ : ∀ i, IsAdditive (ψ i) := by
        intro i
        by_cases hi : i = j
        · simpa [ψ, hi] using (isAdditive_X (k := k))
        · simpa [ψ, hi] using (isAdditive_zero (k := k))
      refine ⟨ψ, ψ, hψ, hψ, ?_, ?_⟩
      · apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i = j
        · simp [ψ, hi, hj]
        · simp [ψ, hi, (hf i).comp_zero]
      · calc
          (∑ i, (ψ i).comp (ψ i)) = ∑ i, ψ i := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i = j <;> simp [ψ, hi]
          _ = X := by simp [ψ]

/-- A pointed nonzero kernel curve yields an additive polynomial section with
an additive polynomial left inverse. -/
theorem hasSplitAdditiveKernelCurve_of_pointed
    (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : ι → k[X]) (hφ : ∀ i, (φ i).coeff 0 = 0) (hφ0 : φ ≠ 0)
    (hrel : (∑ i, (f i).comp (φ i)) = 0) : HasSplitAdditiveKernelCurve f :=
  hasSplitAdditiveKernelCurve_aux (ringExpChar k) _ f le_rfl hf φ hφ hφ0 hrel

/-- Every nonconstant polynomial curve in an additive separated-variable kernel
yields a split additive polynomial curve over the original field. -/
theorem hasSplitAdditiveKernelCurve_of_nonconstant
    (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : ι → k[X]) (hφ : ∃ i, 0 < (φ i).natDegree)
    (hrel : (∑ i, (f i).comp (φ i)) = 0) : HasSplitAdditiveKernelCurve f := by
  obtain ⟨ψ, hψ0, hψ, hψrel⟩ := exists_additive_kernel_curve f hf φ hφ hrel
  exact hasSplitAdditiveKernelCurve_of_pointed f hf ψ (fun i => (hψ i).coeff_zero) hψ0 hψrel

section Evaluation

variable {R : Type w} [CommRing R] [Algebra k R]

/-- Evaluating a separated-variable composition sum agrees with applying the
row to the evaluated polynomial tuple. -/
theorem sum_aeval_aeval (r ψ : ι → k[X]) (x : R) :
    (∑ i, aeval (aeval x (ψ i)) (r i)) =
      aeval x (∑ i, (r i).comp (ψ i)) := by
  simp only [map_sum, aeval_comp]

/-- A polynomial kernel relation holds on every commutative coefficient
algebra, including algebras with nilpotents. -/
theorem sum_aeval_aeval_eq_zero (f ψ : ι → k[X])
    (hrel : (∑ i, (f i).comp (ψ i)) = 0) (x : R) :
    (∑ i, aeval (aeval x (ψ i)) (f i)) = 0 := by
  rw [sum_aeval_aeval, hrel, map_zero]

/-- A polynomial retraction identity gives a left inverse on every
commutative coefficient algebra. -/
theorem aeval_tuple_leftInverse (ψ r : ι → k[X])
    (hret : (∑ i, (r i).comp (ψ i)) = X) :
    Function.LeftInverse (fun y : ι → R => ∑ i, aeval (y i) (r i))
      (fun x : R => fun i => aeval x (ψ i)) := by
  intro x
  change (∑ i, aeval (aeval x (ψ i)) (r i)) = x
  rw [sum_aeval_aeval, hret, aeval_X]

/-- The section defined by a polynomial retraction is injective on every
commutative coefficient algebra. -/
theorem aeval_tuple_injective (ψ r : ι → k[X])
    (hret : (∑ i, (r i).comp (ψ i)) = X) :
    Function.Injective (fun x : R => fun i => aeval x (ψ i)) :=
  (aeval_tuple_leftInverse ψ r hret).injective

end Evaluation

end Langlands.GroupScheme.Unipotent

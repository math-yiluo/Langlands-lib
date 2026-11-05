import Langlands.GroupScheme.Unipotent.AdditiveKernelRetraction
import Langlands.GroupScheme.Unipotent.PrincipalPartDescent

/-! # Galois descent of split additive polynomial kernel curves -/

noncomputable section

universe u v w

open Polynomial
open scoped BigOperators

namespace Langlands.GroupScheme.Unipotent

open OneDimensional

variable {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K]
  {ι : Type w} [Fintype ι]

/-- A nonconstant polynomial curve in a separated-variable polynomial kernel. -/
def HasNonconstantPolynomialKernelCurve (f : ι → k[X]) : Prop :=
  ∃ φ : ι → k[X], (∃ i, 0 < (φ i).natDegree) ∧
    (∑ i, (f i).comp (φ i)) = 0

/-- Additivity as a polynomial identity is preserved by extension of scalars. -/
theorem OneDimensional.IsAdditive.map_algebraMap {f : k[X]} (hf : IsAdditive f) :
    IsAdditive (f.map (algebraMap k K)) := by
  apply isAdditive_of_aeval
  simpa only [← aeval_eq_aeval_map (IsScalarTower.algebraMap_eq k K K[X][X]).symm]
    using hf.aeval_add (C X : K[X][X]) X

/-- Scalar extension preserves the section and the retraction identities. -/
theorem HasSplitAdditiveKernelCurve.map_algebraMap {f : ι → k[X]}
    (h : HasSplitAdditiveKernelCurve f) :
    HasSplitAdditiveKernelCurve (fun i => (f i).map (algebraMap k K)) := by
  obtain ⟨ψ, r, hψ, hr, hrel, hret⟩ := h
  refine ⟨fun i => (ψ i).map (algebraMap k K),
    fun i => (r i).map (algebraMap k K),
    fun i => (hψ i).map_algebraMap, fun i => (hr i).map_algebraMap, ?_, ?_⟩
  · simpa only [Polynomial.map_sum, Polynomial.map_comp, Polynomial.map_zero] using
      congrArg (Polynomial.map (algebraMap k K)) hrel
  · simpa only [Polynomial.map_sum, Polynomial.map_comp, Polynomial.map_X] using
      congrArg (Polynomial.map (algebraMap k K)) hret

/-- A split additive kernel curve is nonconstant, since its retraction is X. -/
theorem HasSplitAdditiveKernelCurve.hasNonconstantPolynomialKernelCurve
    {f : ι → k[X]} (h : HasSplitAdditiveKernelCurve f) :
    HasNonconstantPolynomialKernelCurve f := by
  obtain ⟨ψ, r, hψ, hr, hrel, hret⟩ := h
  refine ⟨ψ, ?_, hrel⟩
  by_contra hn
  have hψ0 : ψ = 0 := by
    funext i
    have hd : (ψ i).natDegree = 0 := by
      have := not_exists.mp hn i
      omega
    rw [eq_C_of_natDegree_eq_zero hd, (hψ i).coeff_zero, C_0]
    rfl
  have hz : (∑ i, (r i).comp (ψ i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hψ0]
    exact (hr i).comp_zero
  exact X_ne_zero (hret.symm.trans hz)

/-- For additive equations, a nonconstant kernel curve is equivalent to a
split additive polynomial curve over the same field. -/
theorem hasSplitAdditiveKernelCurve_iff_hasNonconstantPolynomialKernelCurve
    (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    HasSplitAdditiveKernelCurve f ↔ HasNonconstantPolynomialKernelCurve f := by
  constructor
  · exact HasSplitAdditiveKernelCurve.hasNonconstantPolynomialKernelCurve
  · rintro ⟨φ, hφ, hrel⟩
    exact hasSplitAdditiveKernelCurve_of_nonconstant f hf φ hφ hrel

/-- A split additive kernel curve in the transformed equation returns to a
split additive curve by an invertible additive shear over the same field. -/
theorem HasSplitAdditiveKernelCurve.of_polynomialShear [DecidableEq ι]
    (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i)) (j : ι) (a : k) (ha : a ≠ 0)
    (q : ι → k[X]) (hqj : q j = C a * X) (hq : ∀ i, IsAdditive (q i))
    (h : HasSplitAdditiveKernelCurve
      (fun i => if i = j then ∑ l, (f l).comp (q l) else f i)) :
    HasSplitAdditiveKernelCurve f := by
  classical
  obtain ⟨ψ', r', hψ', hr', hrel', hret'⟩ := h
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
    exact hrel'
  · change (∑ i, (if i = j then ∑ l, (r' l).comp (qinv l) else r' i).comp
      (polynomialShear j q ψ' i)) = X
    rw [← sum_comp_polynomialShear j r' qinv (polynomialShear j q ψ') hr']
    change (∑ i, (r' i).comp (polynomialShear j
      (polynomialShearInverseCoordinates j a q) (polynomialShear j q ψ') i)) = X
    rw [← polynomialShearInverse_eq_shear j a q (polynomialShear j q ψ'),
      polynomialShearInverse_shear j a ha q ψ' hqj]
    exact hret'

/-- The principal zero extracted from a nonconstant kernel curve over a Galois
extension descends to the coefficient field when the equation coordinates are
nonzero additive polynomials. -/
theorem exists_principalPart_zero_of_galois_curve (p : ℕ) [ExpChar k p]
    [IsGalois k K] (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i))
    (hf0 : ∀ i, f i ≠ 0) (φ : ι → K[X]) (hφ : ∃ i, 0 < (φ i).natDegree)
    (hrel : (∑ i, ((f i).map (algebraMap k K)).comp (φ i)) = 0) :
    ∃ b : ι → k, b ≠ 0 ∧
      (∑ i, (f i).leadingCoeff * b i ^ (f i).natDegree) = 0 := by
  obtain ⟨b, hb, hbeq⟩ := exists_principalPart_zero_of_sum_comp_eq_zero
    (fun i => (f i).map (algebraMap k K)) φ
    (fun i => by simp only [coeff_map, (hf i).coeff_zero, map_zero]) hφ hrel
  choose m hm using fun i => (hf i).natDegree_eq_pow p (hf0 i)
  have hbeq' : (∑ i, algebraMap k K ((f i).leadingCoeff) * b i ^ (p ^ m i)) = 0 := by
    simpa only [Polynomial.leadingCoeff_map_of_injective (algebraMap k K).injective,
      Polynomial.natDegree_map_eq_of_injective (algebraMap k K).injective, hm] using hbeq
  obtain ⟨c, hc, hceq⟩ :=
    (exists_nonzero_powerSum_zero_iff_of_isGalois p (fun i => (f i).leadingCoeff) m).mp
      ⟨b, hb, hbeq'⟩
  exact ⟨c, hc, by simpa only [hm] using hceq⟩

private theorem hasSplitAdditiveKernelCurve_galois_aux (p : ℕ) [ExpChar k p]
    [IsGalois k K] :
    ∀ N : ℕ, ∀ f : ι → k[X], (∑ i, (f i).natDegree) ≤ N →
      (∀ i, IsAdditive (f i)) →
      ∀ φ : ι → K[X], (∀ i, (φ i).coeff 0 = 0) → φ ≠ 0 →
      (∑ i, ((f i).map (algebraMap k K)).comp (φ i)) = 0 →
      HasSplitAdditiveKernelCurve f := by
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
      obtain ⟨b, hb0, hb⟩ :=
        exists_principalPart_zero_of_galois_curve p f hf hf0 φ hφpos hrel
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
      let fK : ι → K[X] := fun i => (f i).map (algebraMap k K)
      let qK : ι → K[X] := fun i => (q i).map (algebraMap k K)
      have hfK : ∀ i, IsAdditive (fK i) := fun i => (hf i).map_algebraMap
      have hqK : ∀ i, IsAdditive (qK i) := fun i => (hq i).map_algebraMap
      have hqKj : qK j = C (algebraMap k K a) * X := by simp [qK, hqj]
      have haK : algebraMap k K a ≠ 0 := by
        simpa only [map_zero] using (algebraMap k K).injective.ne ha
      let φ' := polynomialShearInverse j (algebraMap k K a) qK φ
      have hφ' : ∀ i, (φ' i).coeff 0 = 0 :=
        polynomialShearInverse_coeff_zero j (algebraMap k K a) qK φ
          (fun i => (hqK i).coeff_zero) hφ
      have hφ'0 : φ' ≠ 0 := by
        intro hz
        have hinv : polynomialShear j qK φ' = φ :=
          polynomialShear_inverse j (algebraMap k K a) haK qK φ hqKj
        rw [hz, polynomialShear_zero j qK hqK] at hinv
        exact hφ0 hinv.symm
      have hrel' : (∑ i, ((f' i).map (algebraMap k K)).comp (φ' i)) = 0 := by
        calc
          (∑ i, ((f' i).map (algebraMap k K)).comp (φ' i)) =
              ∑ i, (fK i).comp (polynomialShear j qK φ' i) := by
            rw [sum_comp_polynomialShear j fK qK φ' hfK]
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : i = j <;>
              simp [f', g, fK, qK, hi, Polynomial.map_sum, Polynomial.map_comp]
          _ = 0 := by
            change (∑ i, (fK i).comp (polynomialShear j qK
              (polynomialShearInverse j (algebraMap k K a) qK φ) i)) = 0
            rw [polynomialShear_inverse j (algebraMap k K a) haK qK φ hqKj]
            exact hrel
      have hsplit := ih _ (hsum.trans_le hN) f' le_rfl hf' φ' hφ' hφ'0 hrel'
      exact hsplit.of_polynomialShear f hf j a ha q hqj hq
    · obtain ⟨j, hj⟩ : ∃ j, f j = 0 := by simpa using hf0
      apply hasSplitAdditiveKernelCurve_of_nonconstant f hf
        (fun i => if i = j then X else 0)
      · exact ⟨j, by simp⟩
      · apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i = j
        · simp [hi, hj]
        · simp [hi, (hf i).comp_zero]

/-- A pointed nonzero polynomial kernel curve over a Galois extension gives
an additive polynomial section and retraction over the coefficient field. -/
theorem hasSplitAdditiveKernelCurve_of_pointed_galois
    [IsGalois k K] (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : ι → K[X]) (hφ : ∀ i, (φ i).coeff 0 = 0) (hφ0 : φ ≠ 0)
    (hrel : (∑ i, ((f i).map (algebraMap k K)).comp (φ i)) = 0) :
    HasSplitAdditiveKernelCurve f :=
  hasSplitAdditiveKernelCurve_galois_aux (ringExpChar k) _ f le_rfl hf φ hφ hφ0 hrel

/-- A nonconstant polynomial kernel curve over any algebraic Galois extension
gives a split additive polynomial kernel curve over the original field. -/
theorem hasSplitAdditiveKernelCurve_of_nonconstant_galois
    [IsGalois k K] (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i))
    (φ : ι → K[X]) (hφ : ∃ i, 0 < (φ i).natDegree)
    (hrel : (∑ i, ((f i).map (algebraMap k K)).comp (φ i)) = 0) :
    HasSplitAdditiveKernelCurve f := by
  obtain ⟨ψ, hψ0, hψ, hψrel⟩ := exists_additive_kernel_curve
    (fun i => (f i).map (algebraMap k K)) (fun i => (hf i).map_algebraMap) φ hφ hrel
  exact hasSplitAdditiveKernelCurve_of_pointed_galois f hf ψ
    (fun i => (hψ i).coeff_zero) hψ0 hψrel

/-- Existence of a split additive polynomial kernel curve is invariant under
an algebraic Galois extension of the coefficient field. -/
theorem hasSplitAdditiveKernelCurve_iff_of_isGalois
    [IsGalois k K] (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    HasSplitAdditiveKernelCurve (fun i => (f i).map (algebraMap k K)) ↔
      HasSplitAdditiveKernelCurve f := by
  constructor
  · intro h
    obtain ⟨φ, hφ, hrel⟩ := h.hasNonconstantPolynomialKernelCurve
    exact hasSplitAdditiveKernelCurve_of_nonconstant_galois f hf φ hφ hrel
  · exact HasSplitAdditiveKernelCurve.map_algebraMap

/-- Existence of a nonconstant polynomial kernel curve is invariant under an
algebraic Galois extension for additive separated-variable equations. -/
theorem hasNonconstantPolynomialKernelCurve_iff_of_isGalois
    [IsGalois k K] (f : ι → k[X]) (hf : ∀ i, IsAdditive (f i)) :
    HasNonconstantPolynomialKernelCurve (fun i => (f i).map (algebraMap k K)) ↔
      HasNonconstantPolynomialKernelCurve f := by
  rw [← hasSplitAdditiveKernelCurve_iff_hasNonconstantPolynomialKernelCurve _
    (fun i => (hf i).map_algebraMap),
    ← hasSplitAdditiveKernelCurve_iff_hasNonconstantPolynomialKernelCurve f hf]
  exact hasSplitAdditiveKernelCurve_iff_of_isGalois f hf

end Langlands.GroupScheme.Unipotent

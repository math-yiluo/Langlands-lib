import Langlands.Algebra.DegreeDeterminant.Core

/-! # The degree of an endomorphism is a determinant: conclusion

This module finishes the algebraic part of Milne's proof of Proposition 12.9 of
*Abelian Varieties*: under `DegreeData ρ δ iso`, `δ α = det (ρ α)` for every `α`.
-/

noncomputable section

open Polynomial

namespace Langlands.Algebra.DegreeDeterminant

section Matrix

variable {L : Type*} [Field L] [IsAlgClosed L] {g : ℕ}

/-- Milne's Lemma 12.11 for the determinant of `F(A)`. -/
theorem det_aeval_eq_prod_roots (A : Matrix (Fin (2 * g)) (Fin (2 * g)) L) (F : L[X]) :
    (aeval A F).det = (A.charpoly.roots.map fun q => F.eval q).prod := by
  apply eq_prod_eval_roots F.natDegree (2 * g) (even_two_mul g) (fun G => (aeval A G).det)
  · intro G H _ _
    rw [map_mul, Matrix.det_mul]
  · intro c
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin]
  · exact Matrix.charpoly_monic A
  · rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · intro x
    rw [Matrix.eval_charpoly, map_sub, aeval_X, aeval_C, Matrix.algebraMap_eq_diagonal,
      Matrix.scalar_apply, ← neg_sub, Matrix.det_neg, Fintype.card_fin, (even_two_mul g).neg_one_pow,
      one_mul]
    rfl
  · exact le_rfl

end Matrix

section Integral

variable {p : ℕ} [Fact p.Prime]

/-- Every `p`-adic polynomial has a nonzero multiple with integral coefficients. -/
theorem exists_integral_multiple (π : ℚ_[p][X]) :
    ∃ c : ℚ_[p], c ≠ 0 ∧ ∀ i, ‖(C c * π).coeff i‖ ≤ 1 := by
  let B : ℝ := ∑ i ∈ Finset.range (π.natDegree + 1), ‖π.coeff i‖
  have hB : ∀ i, ‖π.coeff i‖ ≤ B := by
    intro i
    by_cases hi : i ≤ π.natDegree
    · exact Finset.single_le_sum (f := fun i => ‖π.coeff i‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (B + 1))
    (inv_lt_one_of_one_lt₀ hp1)
  refine ⟨(p : ℚ_[p]) ^ N, pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero),
    fun i => ?_⟩
  rw [coeff_C_mul, norm_mul, norm_pow, Padic.norm_p]
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc (p : ℝ)⁻¹ ^ N * ‖π.coeff i‖ ≤ (1 / (B + 1)) * (B + 1) := by
        apply mul_le_mul hN.le (by linarith [hB i]) (norm_nonneg _) (by positivity)
    _ = 1 := by field_simp

end Integral

/-- `coeffEval M` along the line `t ↦ F + C t`, as a polynomial in `t`. -/
theorem coeffEval_add_C_eq {N : ℕ} (M : MvPolynomial (Fin N) ℚ) {S : Type*} [CommRing S]
    [Algebra ℚ S] (F : S[X]) (t : S) :
    coeffEval M (F + C t) = (MvPolynomial.aeval (fun k : Fin N =>
      C (F.coeff k) + if (k : ℕ) = 0 then (X : S[X]) else 0) M).eval t := by
  have h := MvPolynomial.comp_aeval_apply
    ((Polynomial.aeval t).restrictScalars ℚ : S[X] →ₐ[ℚ] S)
    (f := fun k : Fin N => C (F.coeff k) + if (k : ℕ) = 0 then (X : S[X]) else 0) M
  rw [AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval] at h
  rw [h, coeffEval]
  refine congrArg (fun v => MvPolynomial.aeval v M) (funext fun k => ?_)
  rw [coeff_add, coeff_C]
  split_ifs <;> simp

theorem coeffEval_map_algebraMap {N : ℕ} (M : MvPolynomial (Fin N) ℚ) {S T : Type*}
    [CommRing S] [CommRing T] [Algebra ℚ S] [Algebra ℚ T] [Algebra S T] [IsScalarTower ℚ S T]
    (F : S[X]) : coeffEval M (F.map (algebraMap S T)) = algebraMap S T (coeffEval M F) :=
  coeffEval_map M (IsScalarTower.toAlgHom ℚ S T) F

section Main

variable {R : Type*} [Ring R] {p : ℕ} [Fact p.Prime] {g : ℕ}
  {ρ : R →+* Matrix (Fin (2 * g)) (Fin (2 * g)) ℚ_[p]} {δ : R → ℚ} {iso : R → Prop}
  (α : R) {M : MvPolynomial (Fin (2 * (2 * g + 1) + 1)) ℚ}

/-- The `p`-adic norms of the two polynomial functions agree at integral points where the
determinant does not vanish. -/
theorem norm_coeffEval_eq (hD : DegreeData ρ δ iso)
    (hM : ∀ x : Fin (2 * (2 * g + 1) + 1) → ℕ,
      δ (aeval α (ofCoeffs x)) = MvPolynomial.eval (fun i => (x i : ℚ)) M)
    (F : ℚ_[p][X]) (hF : F.natDegree < 2 * (2 * g + 1) + 1) (hint : ∀ i, ‖F.coeff i‖ ≤ 1)
    (hdet : (aeval (ρ α) F).det ≠ 0) :
    ‖coeffEval M F‖ = ‖(aeval (ρ α) F).det‖ := by
  let E : MvPolynomial (Fin (2 * (2 * g + 1) + 1)) ℚ_[p] :=
    edet (ρ α) (fun k => MvPolynomial.X k)
  have hEval : ∀ y, MvPolynomial.eval y E = edet (ρ α) y := by
    intro y
    change MvPolynomial.aeval y E = _
    rw [map_edet]
    simp
  have hPval : ∀ y, MvPolynomial.eval y (MvPolynomial.map (algebraMap ℚ ℚ_[p]) M) =
      MvPolynomial.aeval y M := by
    intro y
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
  have hA : (ρ α).map (algebraMap ℚ_[p] ℚ_[p]) = ρ α := by
    ext i j
    simp
  have hEF : edet (ρ α) (fun k : Fin (2 * (2 * g + 1) + 1) => F.coeff k) =
      (aeval (ρ α) F).det := by
    rw [edet_eq, hA, ofCoeffs_coeff F hF]
  have h := norm_eval_eq_of_natCast (MvPolynomial.map (algebraMap ℚ ℚ_[p]) M) E ?_
    (fun k => F.coeff k) (fun k => hint k) (by rw [hEval, hEF]; exact hdet)
  · rw [hPval, hEval, hEF] at h
    exact h
  · intro x hx
    rw [hEval, edet_natCast] at hx ⊢
    have hx' : (MvPolynomial.aeval fun i => ((x i : ℕ) : ℚ_[p])) M =
        algebraMap ℚ ℚ_[p] (δ (aeval α (ofCoeffs x))) := by
      rw [hM x, algebraMap_eval]
      congr 1
    rw [hPval, hx', eq_ratCast]
    exact hD.norm _ (hD.iso_of_det_ne_zero hx)

/-- The algebraic part of Milne's Proposition 12.9: under `DegreeData`, `δ α = det (ρ α)`. -/
theorem DegreeData.det_eq (hD : DegreeData ρ δ iso) : (δ α : ℚ_[p]) = (ρ α).det := by
  classical
  obtain ⟨M, hM⟩ := hD.exists_mvPolynomial α (2 * (2 * g + 1) + 1)
  let A := ρ α
  let L := AlgebraicClosure ℚ_[p]
  let AL : Matrix (Fin (2 * g)) (Fin (2 * g)) L := A.map (algebraMap ℚ_[p] L)
  obtain ⟨hQmon, hQdeg⟩ := lineQ_monic α hD hM
  have hΔ : ∀ F : L[X], F.natDegree ≤ 2 * g + 1 → coeffEval M F =
      (((lineQ M).map (algebraMap ℚ L)).roots.map fun q => F.eval q).prod := by
    intro F hF
    apply eq_prod_eval_roots (2 * g + 1) (2 * g) (even_two_mul g) (coeffEval M)
    · intro G H hG hH
      exact coeffEval_mul α hD hM L G H hG hH
    · intro c
      exact coeffEval_C α hD hM L c
    · exact hQmon.map _
    · rw [natDegree_map, hQdeg]
    · intro x
      rw [coeffEval_X_sub_C, aeval_def, eval₂_eq_eval_map]
    · exact hF
  have hE : ∀ F : L[X], (aeval AL F).det =
      ((A.charpoly.map (algebraMap ℚ_[p] L)).roots.map fun q => F.eval q).prod := by
    intro F
    rw [det_aeval_eq_prod_roots, Matrix.charpoly_map]
  have hdetmap : ∀ F : ℚ_[p][X], algebraMap ℚ_[p] L (aeval A F).det =
      (aeval AL (F.map (algebraMap ℚ_[p] L))).det := by
    intro F
    rw [RingHom.map_det, RingHom.mapMatrix_apply, aeval_map_algebraMap]
    congr 1
    have h := Polynomial.aeval_algHom_apply
      ((Algebra.ofId ℚ_[p] L).mapMatrix (m := Fin (2 * g))) A F
    rw [AlgHom.mapMatrix_apply] at h
    exact h.symm
  have hinfK : Set.Infinite (Set.range (algebraMap ℚ_[p] L)) :=
    Set.infinite_range_of_injective (algebraMap ℚ_[p] L).injective
  have hcount : ∀ π : ℚ_[p][X], π.Monic → Irreducible π → π.natDegree ≤ 2 * g + 1 →
      rootCount L ((lineQ M).map (algebraMap ℚ ℚ_[p])) π = rootCount L A.charpoly π := by
    intro π _ _ hπdeg
    obtain ⟨c, hc0, hcint⟩ := exists_integral_multiple π
    let π' := C c * π
    have hπ'deg : π'.natDegree ≤ 2 * g + 1 := (natDegree_C_mul_le _ _).trans hπdeg
    have hdegt : ∀ t : ℚ_[p], (π' + C t).natDegree ≤ 2 * g + 1 := fun t =>
      (natDegree_add_le _ _).trans (max_le hπ'deg (by rw [natDegree_C]; omega))
    let u : ℚ_[p][X] := MvPolynomial.aeval (fun k : Fin (2 * (2 * g + 1) + 1) =>
      C (π'.coeff k) + if (k : ℕ) = 0 then (X : ℚ_[p][X]) else 0) M
    have hu : ∀ t, u.eval t = coeffEval M (π' + C t) := fun t =>
      (coeffEval_add_C_eq M π' t).symm
    let v : ℚ_[p][X] := (-(aeval A π')).charpoly
    have hv : ∀ t, v.eval t = (aeval A (π' + C t)).det := by
      intro t
      rw [Matrix.eval_charpoly, sub_neg_eq_add, map_add, aeval_C, Matrix.algebraMap_eq_diagonal,
        Matrix.scalar_apply, add_comm]
      rfl
    have hprod : ∀ (Q w : ℚ_[p][X]), (∀ t : ℚ_[p], algebraMap ℚ_[p] L (w.eval t) =
        ((Q.map (algebraMap ℚ_[p] L)).roots.map fun q =>
          ((π' + C t).map (algebraMap ℚ_[p] L)).eval q).prod) →
        rootMultiplicity 0 w = rootCount L Q π := by
      intro Q w hw
      have hmap : w.map (algebraMap ℚ_[p] L) = ((Q.map (algebraMap ℚ_[p] L)).roots.map
          fun q => X + C ((π'.map (algebraMap ℚ_[p] L)).eval q)).prod := by
        apply Polynomial.eq_of_infinite_eval_eq
        refine hinfK.mono ?_
        rintro _ ⟨t, rfl⟩
        simp only [Set.mem_ofPred_eq]
        rw [eval_map_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval, hw t,
          eval_multiset_prod, Multiset.map_map]
        congr 1
        refine Multiset.map_congr rfl fun q _ => ?_
        simp [Polynomial.map_add, add_comm]
      rw [eq_rootMultiplicity_map (algebraMap ℚ_[p] L).injective, map_zero, hmap,
        rootMultiplicity_zero_prod, rootCount]
      congr 1
      apply Multiset.filter_congr
      intro q _
      simp only [π', Polynomial.map_mul, Polynomial.map_C, eval_mul, eval_C, mul_eq_zero,
        eval_map_algebraMap]
      have : algebraMap ℚ_[p] L c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      simp [this]
    have hu' : rootMultiplicity 0 u = rootCount L ((lineQ M).map (algebraMap ℚ ℚ_[p])) π := by
      apply hprod
      intro t
      rw [hu, ← coeffEval_map_algebraMap, hΔ _ ((natDegree_map_le).trans (hdegt t)),
        Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hv' : rootMultiplicity 0 v = rootCount L A.charpoly π := by
      apply hprod
      intro t
      rw [hv, hdetmap, hE]
    rw [← hu', ← hv']
    apply rootMultiplicity_zero_eq_of_norm_eval_eq u v (Matrix.charpoly_monic _).ne_zero
    intro t ht hvt
    rw [hu, hv] at *
    apply norm_coeffEval_eq α hD hM (π' + C t) (by have := hdegt t; omega) ?_ hvt
    intro i
    rw [coeff_add, coeff_C]
    refine (Padic.nonarchimedean _ _).trans (max_le (hcint i) ?_)
    split_ifs
    · exact ht
    · simp
  have hQχ : (lineQ M).map (algebraMap ℚ ℚ_[p]) = A.charpoly :=
    eq_of_rootCount_eq L (2 * g + 1) _ _ _ rfl (hQmon.map _) (Matrix.charpoly_monic _)
      (by rw [natDegree_map, hQdeg]; omega)
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega) hcount
  have hX : coeffEval M (X : L[X]) = (aeval AL (X : L[X])).det := by
    rw [hΔ X (by rw [natDegree_X]; omega), hE X, ← hQχ, Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq]
  have hXK : coeffEval M (X : ℚ_[p][X]) = (δ α : ℚ_[p]) := by
    have h := coeffEval_natCast M δ α hM (S := ℚ_[p]) X (by rw [natDegree_X]; omega)
    rw [Polynomial.map_X, aeval_X, eq_ratCast] at h
    exact h
  apply (algebraMap ℚ_[p] L).injective
  rw [← hXK, ← coeffEval_map_algebraMap, Polynomial.map_X, hX, ← Polynomial.map_X
    (algebraMap ℚ_[p] L), ← hdetmap, aeval_X]

end Main

end Langlands.Algebra.DegreeDeterminant

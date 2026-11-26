import Langlands.BushnellKutzko.FiltrationCoordinates
import Langlands.BushnellKutzko.UnitFiltration
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Determinants to first order at filtered depths -/

open ValuativeRel Polynomial

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]

private theorem ordOf_finset_prod {π : 𝒪[F]} (hπ : Irreducible π) {ι : Type*}
    (s : Finset ι) (a : ι → F) (ha : ∀ i ∈ s, a i ≠ 0) :
    ordOf hπ (∏ i ∈ s, a i) = ∑ i ∈ s, ordOf hπ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ordOf_one hπ]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, a j ≠ 0 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      ordOf_mul hπ (ha i (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

namespace LatticeChain

/-- The trace gives the linear term of the determinant, with all terms of degree
at least two having uniformizer order at least `d` if `e (d−1) < 2k`. -/
theorem det_one_add_sub_trace_scaled_mem_integer (L : LatticeChain 𝒪[F] F V)
    {π : 𝒪[F]} (hπ : Irreducible π) {k d : ℤ} (hk : 0 ≤ k)
    (hd : (L.period : ℤ) * (d - 1) < 2 * k) {x : Module.End F V}
    (hx : x ∈ L.endFiltration k) :
    ((π : F) ^ (-d) * (LinearMap.det (1 + x) - 1 - LinearMap.trace F V x)) ∈ 𝒪[F] := by
  classical
  let := L.finiteDimensional
  obtain ⟨r, b, hb⟩ := L.exists_basis_splits hπ
  let M := LinearMap.toMatrix b b x
  let P := Matrix.det (1 + (X : F[X]) • M.map C)
  have hcoeff (j : ℕ) (hj : 2 ≤ j) : (π : F) ^ (-d) * P.coeff j ∈ 𝒪[F] := by
    change (π : F) ^ (-d) * (Matrix.det (1 + (X : F[X]) • M.map C)).coeff j ∈ 𝒪[F]
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors, Finset.mul_sum]
    refine Subring.sum_mem _ fun s hs => ?_
    have hcard : s.card = j := (Finset.mem_powersetCard.mp hs).2
    rw [Matrix.det_apply', Finset.mul_sum]
    refine Subring.sum_mem _ fun σ _ => ?_
    let a (i : s) := entry b x (σ i : Fin r) i
    simp only [Matrix.submatrix_apply, M, LinearMap.toMatrix_apply]
    change (π : F) ^ (-d) * (((Equiv.Perm.sign σ : ℤ) : F) * ∏ i : s, a i) ∈ 𝒪[F]
    rw [mul_left_comm]
    apply Subring.mul_mem _ (intCast_mem _ _)
    by_cases ha : ∀ i : s, a i ≠ 0
    · have hle (i : s) : k + L.index hπ (b (i : Fin r)) ≤
          (L.period : ℤ) * ordOf hπ (a i) + L.index hπ (b (σ i : Fin r)) :=
        L.le_of_mem_endFiltration hπ hb hx _ _ (ha i)
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hle i)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Equiv.sum_comp σ (fun i : s => L.index hπ (b (i : Fin r)))] at hsum
      have hconst : (∑ _ : s, k) = (j : ℤ) * k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hcard, nsmul_eq_mul]
      rw [hconst] at hsum
      have hbound : 2 * k ≤ (L.period : ℤ) * ∑ i : s, ordOf hπ (a i) := by
        have hj' : (2 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
        exact (mul_le_mul_of_nonneg_right hj' hk).trans (le_of_add_le_add_right hsum)
      have hper : (0 : ℤ) < (L.period : ℤ) := by exact_mod_cast L.period_pos
      have hord : d ≤ ∑ i : s, ordOf hπ (a i) := by
        have h := (mul_lt_mul_iff_right₀ hper).mp (hd.trans_le hbound)
        omega
      have hp : (∏ i : s, a i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => ha i
      apply mem_integer_of_ordOf_nonneg hπ (mul_ne_zero (zpow_ne_zero _ (coe_uniformizer_ne_zero hπ)) hp)
      rw [ordOf_mul hπ (zpow_ne_zero _ (coe_uniformizer_ne_zero hπ)) hp, ordOf_zpow hπ,
        ordOf_finset_prod hπ Finset.univ a (fun i _ => ha i)]
      omega
    · push Not at ha
      obtain ⟨i, hi⟩ := ha
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]
      exact zero_mem _
  have hrem : LinearMap.det (1 + x) - 1 - LinearMap.trace F V x = P.divX.divX.eval 1 := by
    rw [← LinearMap.det_toMatrix b, map_add, LinearMap.toMatrix_one,
      LinearMap.trace_eq_matrix_trace F b]
    have h : Matrix.det (1 + M) = 1 + M.trace + P.divX.divX.eval 1 := by
      simpa only [one_smul, mul_one, one_pow] using Matrix.det_one_add_smul (1 : F) M
    change Matrix.det (1 + M) - 1 - M.trace = _
    rw [h]
    ring
  rw [hrem, Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [Polynomial.coeff_divX, Polynomial.coeff_divX]
  exact hcoeff (j + 1 + 1) (by omega)

end LatticeChain

end Langlands.BushnellKutzko

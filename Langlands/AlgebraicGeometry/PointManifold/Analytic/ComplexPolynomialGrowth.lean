import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Polynomial growth on complex affine space -/

open scoped BigOperators Nat

namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

private theorem iteratedDeriv_zero_of_polynomialGrowth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {d n : ℕ} (hd : d < n) {C : ℝ}
    (hC : ∀ z, 1 ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ d) :
    iteratedDeriv n f 0 = 0 := by
  by_contra hne
  have hn : 0 < ‖iteratedDeriv n f 0‖ := norm_pos_iff.mpr hne
  let M : ℝ := n.factorial * C
  let R : ℝ := max 1 ((M + 1) / ‖iteratedDeriv n f 0‖)
  have hR : 1 ≤ R := le_max_left _ _
  have hR₀ : 0 < R := zero_lt_one.trans_le hR
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR₀
    (c := 0) (C := C * R ^ d) hf.diffContOnCl (by
      intro z hz
      have hzR : ‖z‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      simpa only [hzR] using hC z (hzR.symm ▸ hR))
  have hscaled := (le_div_iff₀ (pow_pos hR₀ n)).mp hbound
  have hpow : R ^ d * R ≤ R ^ n := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ hR hd
  have hle : ‖iteratedDeriv n f 0‖ * (R ^ d * R) ≤ M * R ^ d :=
    (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans (by
      simpa only [M, mul_assoc] using hscaled)
  have hle' : ‖iteratedDeriv n f 0‖ * R ≤ M := by
    apply (mul_le_mul_iff_right₀ (pow_pos hR₀ d)).mp
    convert hle using 1 <;> ring
  have hgt := (div_le_iff₀ hn).mp
    (le_max_right 1 ((M + 1) / ‖iteratedDeriv n f 0‖))
  change M + 1 ≤ R * ‖iteratedDeriv n f 0‖ at hgt
  rw [mul_comm] at hgt
  linarith

private noncomputable def diagonalPolynomial {ι : Type*} [Fintype ι] {n : ℕ}
    (L : ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) :
    MvPolynomial ι ℂ := by
  classical
  exact ∑ a : Fin n → ι,
    MvPolynomial.C (L fun j => Pi.single (a j) 1) * ∏ j, MvPolynomial.X (a j)

private theorem eval_diagonalPolynomial {ι : Type*} [Fintype ι] {n : ℕ}
    (L : ContinuousMultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) (x : ι → ℂ) :
    MvPolynomial.eval x (diagonalPolynomial L) = L fun _ => x := by
  classical
  have hx : (fun _ : Fin n => x) = fun _ => ∑ i, Pi.single i (x i) := by
    simp only [Finset.univ_sum_single]
  rw [hx]
  change _ = L.toMultilinearMap (fun _ => ∑ i, Pi.single i (x i))
  rw [MultilinearMap.map_sum]
  simp only [diagonalPolynomial, map_sum, map_mul, MvPolynomial.eval_C, map_prod,
    MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro a _
  have hsingle (j : Fin n) : Pi.single (a j) (x (a j)) = x (a j) • Pi.single (a j) 1 := by
    ext i
    by_cases hij : i = a j <;> simp [hij]
  simp only [hsingle, MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
  rfl

/-- An entire function on finite-dimensional complex affine space with polynomial
growth is the evaluation of a multivariate polynomial. -/
theorem exists_mvPolynomial_of_analytic_polynomialGrowth {ι : Type*} [Fintype ι]
    {f : (ι → ℂ) → ℂ} (hf : ∀ x, AnalyticAt ℂ f x)
    {d : ℕ} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C * max 1 ‖x‖ ^ d) :
    ∃ p : MvPolynomial ι ℂ, ∀ x, MvPolynomial.eval x p = f x := by
  obtain ⟨p, hp⟩ := hf 0
  refine ⟨∑ n ∈ Finset.range (d + 1), diagonalPolynomial (p n), fun x => ?_⟩
  let l := ContinuousLinearMap.toSpanSingleton ℂ x
  let g := f ∘ l
  have hg : Differentiable ℂ g := fun z =>
    ((hf (l z)).compContinuousLinearMap (u := l) (x := z)).differentiableAt
  have hC₀ : 0 ≤ C := by simpa using (norm_nonneg (f 0)).trans (hC 0)
  have hgrowth (z : ℂ) (hz : 1 ≤ ‖z‖) : ‖g z‖ ≤ (C * max 1 ‖x‖ ^ d) * ‖z‖ ^ d := by
    have hmax : max 1 ‖l z‖ ≤ ‖z‖ * max 1 ‖x‖ := by
      apply max_le
      · exact hz.trans (le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _))
      · rw [ContinuousLinearMap.toSpanSingleton_apply, norm_smul]
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
    calc
      ‖g z‖ ≤ C * max 1 ‖l z‖ ^ d := hC _
      _ ≤ C * (‖z‖ * max 1 ‖x‖) ^ d := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have hseries : HasFPowerSeriesAt g (p.compContinuousLinearMap l) 0 :=
    HasFPowerSeriesAt.compContinuousLinearMap (u := l) (by simpa [l] using hp)
  obtain ⟨r, hr⟩ := hseries
  have hcoeff (n : ℕ) : p n (fun _ => x) = (n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0 := by
    have hn := hr.factorial_smul (y := (1 : ℂ)) n
    rw [iteratedDeriv_eq_iteratedFDeriv]
    simp only [FormalMultilinearSeries.compContinuousLinearMap,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, l,
      ContinuousLinearMap.toSpanSingleton_apply_one, nsmul_eq_mul] at hn
    rw [← hn, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_mul]
  have ht := Complex.taylorSeries_eq_of_entire' 0 1 hg
  simp only [sub_zero, one_pow, mul_one] at ht
  rw [tsum_eq_sum (s := Finset.range (d + 1))] at ht
  · simpa only [map_sum, eval_diagonalPolynomial, hcoeff, g, Function.comp_apply, l,
      ContinuousLinearMap.toSpanSingleton_apply_one] using ht
  · intro n hn
    rw [iteratedDeriv_zero_of_polynomialGrowth hg (by simpa using hn) hgrowth, mul_zero]

end Langlands.AlgebraicGeometry.PointManifold.Analytic

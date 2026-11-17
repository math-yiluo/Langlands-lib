import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Polynomial.Div

/-! # Analytic comparisons over a normed field

* `rootMultiplicity_zero_eq_of_norm_eval_eq`: two polynomials over a nontrivially normed field
  whose values have the same norm near `0` have the same order of vanishing at `0`.
* `norm_eval_eq_of_natCast`: if two multivariate `p`-adic polynomials have values of the same
  norm at the natural-number points where the second one does not vanish, then they have
  values of the same norm at every point of `ℤ_[p] ^ n` where the second one does not vanish.
-/

noncomputable section

open Polynomial Filter Topology

namespace Langlands.Algebra.DegreeDeterminant

section Order

variable {K : Type*} [NontriviallyNormedField K]

/-- If `‖t‖ ^ a ‖u₁(t)‖ = ‖t‖ ^ b ‖v₁(t)‖` along a sequence tending to `0` through nonzero
values and `u₁(0) ≠ 0`, then `a ≥ b`. -/
theorem not_lt_of_norm_eq (a b : ℕ) (u₁ v₁ : K[X]) (hu : u₁.eval 0 ≠ 0) (t : ℕ → K)
    (ht : Tendsto t atTop (𝓝 0)) (ht0 : ∀ N, t N ≠ 0)
    (heq : ∀ᶠ N in atTop, ‖t N‖ ^ a * ‖u₁.eval (t N)‖ = ‖t N‖ ^ b * ‖v₁.eval (t N)‖) :
    ¬ a < b := by
  intro hab
  have hu' : Tendsto (fun N => ‖u₁.eval (t N)‖) atTop (𝓝 ‖u₁.eval 0‖) :=
    ((u₁.continuous.tendsto 0).comp ht).norm
  have hv' : Tendsto (fun N => ‖t N‖ ^ (b - a) * ‖v₁.eval (t N)‖) atTop
      (𝓝 (‖(0 : K)‖ ^ (b - a) * ‖v₁.eval 0‖)) :=
    ((ht.norm).pow _).mul ((v₁.continuous.tendsto 0).comp ht).norm
  rw [norm_zero, zero_pow (by omega), zero_mul] at hv'
  have heq' : ∀ᶠ N in atTop, ‖u₁.eval (t N)‖ = ‖t N‖ ^ (b - a) * ‖v₁.eval (t N)‖ := by
    filter_upwards [heq] with N hN
    have hpos : 0 < ‖t N‖ ^ a := pow_pos (norm_pos_iff.mpr (ht0 N)) a
    have hb : ‖t N‖ ^ b = ‖t N‖ ^ a * ‖t N‖ ^ (b - a) := by
      rw [← pow_add]; congr 1; omega
    rw [hb, mul_assoc] at hN
    exact mul_left_cancel₀ hpos.ne' hN
  have := tendsto_nhds_unique (hu'.congr' heq') hv'
  exact hu (norm_eq_zero.mp this)

/-- Two polynomials whose values have the same norm at all points of norm at most `1` where
the second does not vanish have the same order of vanishing at `0`. -/
theorem rootMultiplicity_zero_eq_of_norm_eval_eq (u v : K[X]) (hv : v ≠ 0)
    (h : ∀ t : K, ‖t‖ ≤ 1 → v.eval t ≠ 0 → ‖u.eval t‖ = ‖v.eval t‖) :
    rootMultiplicity 0 u = rootMultiplicity 0 v := by
  classical
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  let t : ℕ → K := fun N => c ^ N
  have ht : Tendsto t atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1
  have hc0' : c ≠ 0 := norm_pos_iff.mp hc0
  have ht0 : ∀ N, t N ≠ 0 := fun N => pow_ne_zero N hc0'
  have htle : ∀ N, ‖t N‖ ≤ 1 := fun N => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc1.le
  have htinj : Function.Injective t := by
    intro m n hmn
    have h' : ‖c‖ ^ m = ‖c‖ ^ n := by
      simp only [t] at hmn
      rw [← norm_pow, ← norm_pow, hmn]
    exact (pow_right_strictAnti₀ hc0 hc1).injective h'
  have hvt : ∀ᶠ N in atTop, v.eval (t N) ≠ 0 := by
    have hfin : {N : ℕ | v.eval (t N) = 0}.Finite := by
      refine (Set.Finite.preimage htinj.injOn v.roots.toFinset.finite_toSet).subset ?_
      intro N hN
      simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
      exact (mem_roots hv).mpr hN
    rw [← Nat.cofinite_eq_atTop]
    exact hfin.eventually_cofinite_notMem
  have heq : ∀ᶠ N in atTop, ‖u.eval (t N)‖ = ‖v.eval (t N)‖ := by
    filter_upwards [hvt] with N hN
    exact h (t N) (htle N) hN
  have hu : u ≠ 0 := by
    rintro rfl
    obtain ⟨N, hN1, hN2⟩ := (hvt.and heq).exists
    rw [eval_zero, norm_zero, eq_comm, norm_eq_zero] at hN2
    exact hN1 hN2
  obtain ⟨u₁, hu₁, hnu⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd u hu 0
  obtain ⟨v₁, hv₁, hnv⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd v hv 0
  rw [dvd_iff_isRoot, IsRoot.def] at hnu hnv
  have heq' : ∀ᶠ N in atTop, ‖t N‖ ^ rootMultiplicity 0 u * ‖u₁.eval (t N)‖ =
      ‖t N‖ ^ rootMultiplicity 0 v * ‖v₁.eval (t N)‖ := by
    filter_upwards [heq] with N hN
    rw [hu₁, hv₁] at hN
    simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_zero, norm_mul,
      norm_pow] using hN
  have h1 := not_lt_of_norm_eq _ _ u₁ v₁ hnu t ht ht0 heq'
  have h2 := not_lt_of_norm_eq _ _ v₁ u₁ hnv t ht ht0 (heq'.mono fun N hN => hN.symm)
  omega

end Order

section Density

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- Comparison of norms of two `p`-adic multivariate polynomials, from the natural-number
points to the points of `ℤ_[p] ^ n`, away from the zeros of the second one. -/
theorem norm_eval_eq_of_natCast (P E : MvPolynomial (Fin n) ℚ_[p])
    (h : ∀ x : Fin n → ℕ, MvPolynomial.eval (fun i => (x i : ℚ_[p])) E ≠ 0 →
      ‖MvPolynomial.eval (fun i => (x i : ℚ_[p])) P‖ =
        ‖MvPolynomial.eval (fun i => (x i : ℚ_[p])) E‖)
    (y : Fin n → ℚ_[p]) (hy : ∀ i, ‖y i‖ ≤ 1) (hE : MvPolynomial.eval y E ≠ 0) :
    ‖MvPolynomial.eval y P‖ = ‖MvPolynomial.eval y E‖ := by
  let ι : (Fin n → ℤ_[p]) → (Fin n → ℚ_[p]) := fun w i => (w i : ℚ_[p])
  have hι : Continuous ι := continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)
  let f₁ : (Fin n → ℤ_[p]) → ℝ := fun w => ‖MvPolynomial.eval (ι w) P‖
  let f₂ : (Fin n → ℤ_[p]) → ℝ := fun w => ‖MvPolynomial.eval (ι w) E‖
  have hf₁ : Continuous f₁ := (MvPolynomial.continuous_eval P).comp hι |>.norm
  have hf₂ : Continuous f₂ := (MvPolynomial.continuous_eval E).comp hι |>.norm
  let U : Set (Fin n → ℤ_[p]) := {w | MvPolynomial.eval (ι w) E ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage ((MvPolynomial.continuous_eval E).comp hι)
  let S : Set (Fin n → ℤ_[p]) := Set.range (Pi.map fun _ : Fin n => (Nat.cast : ℕ → ℤ_[p]))
  have hS : Dense S := DenseRange.piMap fun _ => PadicInt.denseRange_natCast
  have heq : Set.EqOn f₁ f₂ (U ∩ S) := by
    rintro w ⟨hwU, x, rfl⟩
    have hιx : ι (Pi.map (fun _ => (Nat.cast : ℕ → ℤ_[p])) x) = fun i => (x i : ℚ_[p]) := by
      funext i
      simp [ι]
    simp only [f₁, f₂, hιx]
    simp only [U, Set.mem_ofPred_eq, hιx] at hwU
    exact h x hwU
  let z : Fin n → ℤ_[p] := fun i => ⟨y i, hy i⟩
  have hz : ι z = y := rfl
  have hzU : z ∈ U := by simpa [U, hz] using hE
  have := heq.closure hf₁ hf₂ (hS.open_subset_closure_inter hU hzU)
  simpa only [f₁, f₂, hz] using this

end Density

end Langlands.Algebra.DegreeDeterminant

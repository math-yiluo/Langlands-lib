import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Schwartz tensors for equal-rank archimedean factorization

Internal constructions used in the equal-rank case of Cogdell's factorization.
-/

noncomputable section
universe u v
open scoped ContDiff
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor

section FiniteTensor

variable {ι : Type u} [Fintype ι] {E : ι → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

private theorem norm_iteratedFDeriv_eval_le (f : ∀ i, SchwartzMap (E i) ℂ)
    (x : ∀ i, E i) (i : ι) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y : ∀ i, E i => f i (y i)) x‖ ≤
      ‖iteratedFDeriv ℝ m (f i) (x i)‖ := by
  let L : (∀ i, E i) →L[ℝ] E i := ContinuousLinearMap.proj i
  have hL : ‖L‖ ≤ 1 :=
    L.opNorm_le_bound zero_le_one fun y => by simpa [L] using norm_le_pi_norm y i
  change ‖iteratedFDeriv ℝ m ((f i) ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right ((f i).smooth ⊤) x (by exact_mod_cast le_top)]
  refine ((iteratedFDeriv ℝ m (f i) (L x)).norm_compContinuousLinearMap_le
    (fun _ => L)).trans ?_
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg L) fun _ _ => hL

omit [∀ i, NormedSpace ℝ (E i)] in
private theorem norm_pow_le_product (x : ∀ i, E i) (k : ℕ) :
    ‖x‖ ^ k ≤ ∏ i, (1 + ‖x i‖) ^ k := by
  classical
  have hB : ‖x‖ ≤ ∏ i, (1 + ‖x i‖) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hi := Finset.le_prod_max_one (Finset.mem_univ i)
      (fun j => (1 : ℝ) + ‖x j‖)
    simp only [max_eq_left (le_add_of_nonneg_right (norm_nonneg _))] at hi
    exact (le_add_of_nonneg_left zero_le_one).trans hi
  simpa only [Finset.prod_pow] using pow_le_pow_left₀ (norm_nonneg x) hB k

private theorem tensor_derivative_bound [DecidableEq ι] (f : ∀ i, SchwartzMap (E i) ℂ)
    (x : ∀ i, E i) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y : ∀ i, E i => ∏ i, f i (y i)) x‖ ≤
      ∑ p ∈ (Finset.univ : Finset ι).sym n,
        ((p : Multiset ι).countPerms : ℝ) *
          ∏ i, ‖iteratedFDeriv ℝ ((p : Multiset ι).count i)
            (fun y : ∀ i, E i => f i (y i)) x‖ := by
  classical
  exact norm_iteratedFDeriv_prod_le (𝕜 := ℝ)
    (u := Finset.univ)
    (f := fun i (y : ∀ j, E j) => f i (y i))
    (N := (↑(⊤ : ℕ∞) : ℕ∞ω))
    (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      ((f i).smooth ⊤).comp
        (ContinuousLinearMap.proj i : (∀ j, E j) →L[ℝ] E i).contDiff)
    (x := x) (n := n) (by exact_mod_cast le_top)

private theorem tensor_weighted_bound (f : ∀ i, SchwartzMap (E i) ℂ)
    (k n : ℕ) (d : ι → ℕ) (hd : ∀ i, d i ≤ n) (x : ∀ i, E i) :
    ‖x‖ ^ k * ∏ i, ‖iteratedFDeriv ℝ (d i)
      (fun y : ∀ i, E i => f i (y i)) x‖ ≤
      ∏ i, 2 ^ k * (Finset.Iic (k, n)).sup
        (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) (f i) := by
  classical
  calc
    ‖x‖ ^ k * ∏ i, ‖iteratedFDeriv ℝ (d i)
        (fun y : ∀ i, E i => f i (y i)) x‖ ≤
        (∏ i, (1 + ‖x i‖) ^ k) *
          ∏ i, ‖iteratedFDeriv ℝ (d i) (f i) (x i)‖ := by
      apply mul_le_mul (norm_pow_le_product x k)
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
          norm_iteratedFDeriv_eval_le f x i (d i)) (by positivity) (by positivity)
    _ = ∏ i, (1 + ‖x i‖) ^ k * ‖iteratedFDeriv ℝ (d i) (f i) (x i)‖ :=
      (Finset.prod_mul_distrib).symm
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro i _
      exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, n))
        (k := k) (n := d i) le_rfl (hd i) (f i) (x i)

/-- The external product of a finite family of Schwartz functions, including the empty
family, as a Schwartz function on the product of their domains. -/
def finiteTensor (f : ∀ i, SchwartzMap (E i) ℂ) : SchwartzMap (∀ i, E i) ℂ where
  toFun x := ∏ i, f i (x i)
  smooth' := by
    classical
    apply contDiff_prod
    intro i _
    exact ((f i).smooth ⊤).comp
      (ContinuousLinearMap.proj i : (∀ j, E j) →L[ℝ] E i).contDiff
  decay' k n := by
    classical
    let C : ι → ℝ := fun i =>
      2 ^ k * (Finset.Iic (k, n)).sup
        (fun p : ℕ × ℕ => SchwartzMap.seminorm ℝ p.1 p.2) (f i)
    refine ⟨∑ p ∈ (Finset.univ : Finset ι).sym n,
      ((p : Multiset ι).countPerms : ℝ) * ∏ i, C i,
      fun x => ?_⟩
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : ∀ i, E i => ∏ i, f i (y i)) x‖ ≤
          ‖x‖ ^ k * ∑ p ∈ (Finset.univ : Finset ι).sym n,
            ((p : Multiset ι).countPerms : ℝ) *
              ∏ i, ‖iteratedFDeriv ℝ ((p : Multiset ι).count i)
                (fun y : ∀ i, E i => f i (y i)) x‖ :=
        mul_le_mul_of_nonneg_left (tensor_derivative_bound f x n) (by positivity)
      _ = ∑ p ∈ (Finset.univ : Finset ι).sym n,
          ((p : Multiset ι).countPerms : ℝ) *
            (‖x‖ ^ k * ∏ i, ‖iteratedFDeriv ℝ ((p : Multiset ι).count i)
              (fun y : ∀ i, E i => f i (y i)) x‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ p ∈ (Finset.univ : Finset ι).sym n,
          ((p : Multiset ι).countPerms : ℝ) * ∏ i, C i := by
        apply Finset.sum_le_sum
        intro p _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact tensor_weighted_bound f k n (fun i => (p : Multiset ι).count i)
          (fun i => (Multiset.count_le_card i _).trans_eq p.card_coe) x

@[simp] theorem finiteTensor_apply (f : ∀ i, SchwartzMap (E i) ℂ) (x : ∀ i, E i) :
    finiteTensor f x = ∏ i, f i (x i) := rfl

end FiniteTensor

end Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor

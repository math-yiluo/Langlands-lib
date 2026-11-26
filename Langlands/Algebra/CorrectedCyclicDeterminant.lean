import Langlands.Algebra.WeightedCyclicDeterminant
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Order.Interval.Finset.Fin

/-! # The determinant of a cyclic defect with a trace section -/

noncomputable section

namespace Langlands.Algebra

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {S : Type w} [AddCommGroup S] [Module K S]

private theorem det_id_add_of_square_zero [FiniteDimensional K V]
    (N : Module.End K V) (hN : N * N = 0) : (1 + N).det = 1 := by
  have hnil : IsNilpotent (-N) := ⟨2, by rw [pow_two, neg_mul_neg, hN]⟩
  simpa only [hnil.charpoly_eq_X_pow_finrank, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    map_one, sub_neg_eq_add] using ((-N).eval_charpoly 1).symm

/-- The negative partial sums, viewed as a linear map on a finite product. -/
private def cyclePrimitive (d : ℕ) : Module.End K (Fin (d + 1) → S) :=
  LinearMap.pi fun i => -∑ j ∈ Finset.Iio i, LinearMap.proj j

private theorem cyclePrimitive_sub {d : ℕ} (x : Fin (d + 1) → S) (i : Fin (d + 1)) :
    cyclePrimitive (K := K) d x i - cyclePrimitive (K := K) d x (finRotate _ i) =
      x i - (if i = Fin.last d then ∑ j, x j else 0) := by
  classical
  change -((∑ j ∈ Finset.Iio i, LinearMap.proj j) x) -
    -((∑ j ∈ Finset.Iio (finRotate _ i), LinearMap.proj j) x) = _
  simp only [LinearMap.sum_apply, LinearMap.proj_apply]
  by_cases hi : i = Fin.last d
  · subst i
    have h : insert (Fin.last d) (Finset.Iio (Fin.last d)) = Finset.univ := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_Iio, Finset.mem_univ, iff_true]
      exact j.le_last.eq_or_lt
    have hz : Finset.Iio (0 : Fin (d + 1)) = ∅ := by ext j; simp
    rw [finRotate_last, ite_eq_left rfl, ← h, Finset.sum_insert (by simp), hz]
    simp
  · have h : Finset.Iio (finRotate _ i) = insert i (Finset.Iio i) := by
      ext j
      simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def,
        coe_finRotate_of_ne_last hi, ← Fin.val_inj]
      omega
    rw [h, ite_eq_right hi, Finset.sum_insert (by simp)]
    abel

private theorem list_prod_apply_fixed (A : List (Module.End K V)) (x : V)
    (h : ∀ a ∈ A, a x = x) : A.prod x = x := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [List.prod_cons, Module.End.mul_apply, ih (fun b hb => h b (List.mem_cons_of_mem a hb)),
      h a (by simp)]

/-- If every weight fixes an embedded subspace pointwise, a quotient
coordinate on its diagonal and a section of the coordinate sum complete the
cyclic defect. The determinant is the determinant of the product defect
completed by the corresponding projection on one copy of the space. -/
theorem det_weightedCycleDefect_add_section
    [FiniteDimensional K V] {d : ℕ}
    (A : Fin (d + 1) → Module.End K V) (i : S →ₗ[K] V) (p : V →ₗ[K] S)
    (hA : ∀ j s, A j (i s) = i s)
    (π : (Fin (d + 1) → V) →ₗ[K] S) (hπ : ∀ s, π (fun _ => i s) = s)
    (hp : ∀ s, p (i s) = s)
    (f : S →ₗ[K] (Fin (d + 1) → S)) (hf : ∀ s, ∑ j, f s j = s) :
    (weightedCycleDefect A + (LinearMap.pi fun j => i.comp ((LinearMap.proj j).comp f)).comp π).det =
      (1 - (List.ofFn A).prod + i.comp p).det := by
  classical
  let U := Fin (d + 1) → V
  let C : S →ₗ[K] U := LinearMap.pi fun _ => i
  let lift : (Fin (d + 1) → S) →ₗ[K] U :=
    LinearMap.pi fun j => i.comp (LinearMap.proj j)
  let s₀ : S →ₗ[K] U := LinearMap.pi fun j => if j = Fin.last d then i else 0
  let π₀ : U →ₗ[K] S := p.comp (LinearMap.proj 0)
  let B := weightedCycleDefect A
  let D₀ := B + s₀.comp π₀
  let D₁ := B + s₀.comp π
  let D := B + (lift.comp f).comp π
  have hC (s : S) : B (C s) = 0 := by
    funext j
    exact sub_eq_zero.mpr (hA j s).symm
  have hπ₀ (s : S) : π₀ (C s) = s := hp s
  have hD₀ (s : S) : D₀ (C s) = s₀ s := by
    change B (C s) + s₀ (π₀ (C s)) = _
    rw [hC, hπ₀, zero_add]
  let N := C.comp (π - π₀)
  have hN : N * N = 0 := by
    apply LinearMap.ext
    intro x
    change C (π (C (π x - π₀ x)) - π₀ (C (π x - π₀ x))) = 0
    rw [show ∀ s, π (C s) = s from hπ, hπ₀, sub_self, map_zero]
  have hD₁ : D₀.comp (1 + N) = D₁ := by
    apply LinearMap.ext
    intro x
    change D₀ (x + C (π x - π₀ x)) = B x + s₀ (π x)
    rw [map_add, hD₀]
    change B x + s₀ (π₀ x) + s₀ (π x - π₀ x) = _
    rw [map_sub]
    abel
  let J := lift.comp ((cyclePrimitive d).comp f)
  have hJ (s : S) : B (J s) = lift (f s) - s₀ s := by
    funext j
    change i (cyclePrimitive (K := K) d (f s) j) -
      A j (i (cyclePrimitive (K := K) d (f s) (finRotate _ j))) =
        i (f s j) - (if j = Fin.last d then i else 0) s
    rw [hA, ← map_sub, cyclePrimitive_sub, hf, map_sub]
    split <;> simp_all
  let J' := J - C.comp (π.comp J)
  have hpJ (s : S) : π (J' s) = 0 := by
    change π (J s - C (π (J s))) = 0
    rw [map_sub, show ∀ t, π (C t) = t from hπ, sub_self]
  have hBJ (s : S) : B (J' s) = lift (f s) - s₀ s := by
    change B (J s - C (π (J s))) = _
    rw [map_sub, hC, sub_zero, hJ]
  let N' := J'.comp π
  have hN' : N' * N' = 0 := by
    apply LinearMap.ext
    intro x
    change J' (π (J' (π x))) = 0
    rw [hpJ, map_zero]
  have hD : D₁.comp (1 + N') = D := by
    apply LinearMap.ext
    intro x
    change D₁ (x + J' (π x)) = B x + lift (f (π x))
    rw [map_add]
    change B x + s₀ (π x) + (B (J' (π x)) + s₀ (π (J' (π x)))) = _
    rw [hpJ, map_zero, add_zero, hBJ]
    abel
  let A₀ := Function.update A (Fin.last d) (A (Fin.last d) - i.comp p)
  have hW : weightedCycleDefect A₀ = D₀ := by
    apply LinearMap.ext
    intro x
    funext j
    change x j - A₀ j (x (finRotate _ j)) =
      (x j - A j (x (finRotate _ j))) + (if j = Fin.last d then i else 0) (p (x 0))
    by_cases hj : j = Fin.last d
    · subst j
      rw [ite_eq_left rfl, finRotate_last]
      simp only [A₀, Function.update_self, LinearMap.sub_apply, LinearMap.comp_apply]
      abel
    · rw [ite_eq_right hj, LinearMap.zero_apply, add_zero]
      simp [A₀, Function.update_of_ne hj]
  let L := (List.ofFn fun j : Fin d => A j.castSucc).prod
  have hL : L * i.comp p = i.comp p := by
    apply LinearMap.ext
    intro x
    change L (i (p x)) = i (p x)
    apply list_prod_apply_fixed
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact hA j.castSucc _
  have hprod : (List.ofFn A₀).prod = (List.ofFn A).prod - i.comp p := by
    rw [List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat]
    simp only [A₀, Function.update_self, Function.update_of_ne (Fin.castSucc_ne_last _)]
    change L * (A (Fin.last d) - i.comp p) = L * A (Fin.last d) - i.comp p
    rw [mul_sub, hL]
  change D.det = _
  rw [← hD, LinearMap.det_comp, det_id_add_of_square_zero _ hN', mul_one,
    ← hD₁, LinearMap.det_comp, det_id_add_of_square_zero _ hN, mul_one,
    ← hW, det_weightedCycleDefect, hprod, sub_sub_eq_add_sub, add_sub_right_comm]

end Langlands.Algebra

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Finite products and determinants of absolutely convergent series -/

noncomputable section

namespace Langlands.Global.EisensteinGenericInjectivity

variable {ι : Type*}

/-- A finite product of absolutely summable families is absolutely summable on tuples. -/
theorem summable_prod_norm_pi : ∀ {m : ℕ} (f : Fin m → ι → ℂ),
    (∀ j, Summable fun c => ‖f j c‖) →
      Summable fun c : Fin m → ι => ∏ j, ‖f j (c j)‖
  | 0, f, _ => by
    simpa using (summable_of_hasFiniteSupport (Set.toFinite _) :
      Summable fun _ : Fin 0 → ι => (1 : ℝ))
  | m + 1, f, hf => by
    have ih := summable_prod_norm_pi (fun j => f j.succ) fun j => hf j.succ
    have hp := Summable.mul_of_nonneg (hf 0) ih (fun c => norm_nonneg _)
      (fun c => Finset.prod_nonneg fun j _ => norm_nonneg _)
    refine (Equiv.summable_iff (Fin.consEquiv fun _ : Fin (m + 1) => ι)).mp ?_
    convert hp using 1
    funext x
    simp [Fin.prod_univ_succ, Fin.consEquiv]

/-- A finite product of absolutely convergent series is the series over tuples of the
products. -/
theorem prod_tsum_eq_tsum_pi : ∀ {m : ℕ} (f : Fin m → ι → ℂ),
    (∀ j, Summable fun c => ‖f j c‖) →
      ∏ j, ∑' c, f j c = ∑' c : Fin m → ι, ∏ j, f j (c j)
  | 0, f, _ => by
    simp
  | m + 1, f, hf => by
    have ih := prod_tsum_eq_tsum_pi (fun j => f j.succ) fun j => hf j.succ
    have hs := summable_prod_norm_pi (fun j => f j.succ) fun j => hf j.succ
    have hs' : Summable fun c : Fin m → ι => ‖∏ j, f j.succ (c j)‖ := by
      simpa [norm_prod] using hs
    rw [Fin.prod_univ_succ, ih, tsum_mul_tsum_of_summable_norm (hf 0) hs',
      ← (Fin.consEquiv fun _ : Fin (m + 1) => ι).tsum_eq]
    congr 1
    funext x
    simp [Fin.prod_univ_succ, Fin.consEquiv]

/-- The determinant of a matrix of absolutely convergent series expands as the series, over
tuples of row indices, of the determinants of the terms. -/
theorem det_tsum {m : ℕ} (T : Fin m → Fin m → ι → ℂ)
    (hT : ∀ j k, Summable fun c => ‖T j k c‖) :
    (Matrix.of fun j k => ∑' c, T j k c).det =
      ∑' c : Fin m → ι, (Matrix.of fun j k => T j k (c j)).det := by
  have hrow : ∀ σ : Equiv.Perm (Fin m), Summable fun c : Fin m → ι => ∏ i, T i (σ i) (c i) :=
    fun σ => Summable.of_norm_bounded (summable_prod_norm_pi (fun i => T i (σ i))
      fun i => hT i (σ i)) fun c => by rw [norm_prod]
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  rw [show (fun c : Fin m → ι => (Matrix.of fun j k => T j k (c j)).det) =
      fun c => ∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ • ∏ i, T i (σ i) (c i) from
    funext fun c => by
      rw [← Matrix.det_transpose, Matrix.det_apply]
      simp only [Matrix.transpose_apply, Matrix.of_apply]]
  rw [Summable.tsum_finsetSum fun σ _ => (hrow σ).const_smul _]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [tsum_const_smul', prod_tsum_eq_tsum_pi (fun i => T i (σ i)) fun i => hT i (σ i)]

/-- The terms of the determinant expansion are absolutely summable. -/
theorem summable_norm_det_pi {m : ℕ} (T : Fin m → Fin m → ι → ℂ)
    (hT : ∀ j k, Summable fun c => ‖T j k c‖) :
    Summable fun c : Fin m → ι => ‖(Matrix.of fun j k => T j k (c j)).det‖ := by
  have hb : Summable fun c : Fin m → ι => ∑ σ : Equiv.Perm (Fin m), ∏ i, ‖T i (σ i) (c i)‖ :=
    summable_sum fun σ _ => summable_prod_norm_pi (fun i => T i (σ i)) fun i => hT i (σ i)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_) hb
  rw [← Matrix.det_transpose, Matrix.det_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [h, norm_prod, Matrix.transpose_apply]

end Langlands.Global.EisensteinGenericInjectivity

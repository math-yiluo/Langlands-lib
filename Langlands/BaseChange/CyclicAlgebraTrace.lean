import Langlands.BaseChange.CyclicAlgebraSplit
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # The additive trace of a cyclic algebra -/

noncomputable section

namespace Langlands.BaseChange

open scoped TensorProduct
open Fin.NatCast

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {l : ℕ}

/-- In split coordinates the sum of the cyclic translates is constant,
with value the sum of the coordinates. -/
theorem sum_cyclic_powers_splitCoordinates
    (e : E ≃ₐ[F] (Fin l → F))
    (h : ∀ x i, e (σ x) i = e x (finRotate l i)) (x : E) (j : Fin l) :
    e (∑ i : Fin l, (σ ^ (i : ℕ)) x) j = ∑ i : Fin l, e x i := by
  let : NeZero l := j.neZero
  have hp (k : ℕ) (j : Fin l) : e ((σ ^ k) x) j = e x (j + (k : Fin l)) := by
    induction k generalizing j with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', AlgEquiv.mul_apply, h, ih, finRotate_apply, Nat.cast_succ,
        add_right_comm, add_assoc]
  rw [map_sum, Finset.sum_apply]
  have hcast (i : Fin l) : ((i : ℕ) : Fin l) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simp_rw [hp, hcast]
  exact Fintype.sum_equiv (Equiv.addLeft j) _ _ (fun _ => rfl)

private theorem linearMap_pow_eq (σ : E ≃ₐ[F] E) (i : ℕ) :
    σ.toLinearMap ^ i = (σ ^ i).toLinearMap := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', ih, pow_succ']
    rfl

private theorem cyclic_sum_fixed (hσ : IsCyclicAlgebra σ l) (x : E) :
    σ (∑ i : Fin l, (σ ^ (i : ℕ)) x) = ∑ i : Fin l, (σ ^ (i : ℕ)) x := by
  cases l with
  | zero => simp
  | succ l =>
    calc
      _ = ∑ i : Fin (l + 1), (σ ^ ((i : ℕ) + 1)) x := by
        simp only [map_sum, pow_succ', AlgEquiv.mul_apply]
      _ = (∑ i : Fin l, (σ ^ ((i : ℕ) + 1)) x) + x := by
        rw [Fin.sum_univ_castSucc]
        simp [hσ.pow_eq_one]
      _ = _ := by rw [Fin.sum_univ_succ]; simp [add_comm]

/-- A cyclic algebra has an element of trace one, including when the
characteristic of the base divides the cyclic degree. -/
theorem IsCyclicAlgebra.exists_cyclic_sum_eq_one (hσ : IsCyclicAlgebra σ l) :
    ∃ x : E, ∑ i : Fin l, (σ ^ (i : ℕ)) x = 1 := by
  classical
  let B := AlgebraicClosure F
  let τ := tensorFactorAut B σ
  obtain ⟨e, he⟩ := hσ.exists_splitCoordinates_baseChange B
  let j : Fin l := ⟨0, hσ.pos⟩
  let t : Module.End F E := ∑ i : Fin l, (σ.toLinearMap ^ (i : ℕ))
  have ht (x : E) : t x = ∑ i : Fin l, (σ ^ (i : ℕ)) x := by
    simp only [t, LinearMap.sum_apply, linearMap_pow_eq, AlgEquiv.toLinearMap_apply]
  have hbase (z : B ⊗[F] E) : t.baseChange B z = ∑ i : Fin l, (τ ^ (i : ℕ)) z := by
    have hτ : σ.toLinearMap.baseChange B = τ.toLinearMap := by
      apply TensorProduct.AlgebraTensorModule.ext
      intro a x
      rfl
    have hcomp := map_sum (Module.End.baseChangeHom F B E)
      (fun i : Fin l => σ.toLinearMap ^ (i : ℕ)) Finset.univ
    change t.baseChange B = ∑ i : Fin l, (σ.toLinearMap ^ (i : ℕ)).baseChange B at hcomp
    rw [hcomp, LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.baseChange_pow, hτ, linearMap_pow_eq]
    rfl
  have hne : t ≠ 0 := by
    intro hz
    let z := e.symm (Pi.single j (1 : B))
    have hsum : e (t.baseChange B z) j = 1 := by
      rw [hbase, sum_cyclic_powers_splitCoordinates e he]
      simp [z, Pi.single_apply]
    simp [hz] at hsum
  obtain ⟨x, hx⟩ : ∃ x, t x ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext h)
  obtain ⟨a, ha⟩ := hσ.2.2.2.2 (t x) (by rw [ht]; exact cyclic_sum_fixed hσ x)
  have ha₀ : a ≠ 0 := fun h => hx (by simp [← ha, h])
  refine ⟨a⁻¹ • x, ?_⟩
  rw [← ht, map_smul, ← ha, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ ha₀, map_one]

end Langlands.BaseChange

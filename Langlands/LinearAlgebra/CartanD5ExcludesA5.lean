import Langlands.LinearAlgebra.ClassicalCartanDeterminants
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-! # A determinant obstruction to type A5 inside type D5 -/

noncomputable section

open Matrix
open scoped BigOperators

namespace Langlands.LinearAlgebra

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootPairing J ℤ X Y}

/-- The determinant of the numbered simple pairing matrix divides every
square pairing determinant of the same size formed from roots and coroots. -/
theorem det_simplePairing_dvd_det_pairing (b : P.Base) {n : ℕ} (e : b.support ≃ Fin n)
    (r s : Fin n → J) :
    (Matrix.of fun i j => P.pairing (e.symm i).val (e.symm j).val).det ∣
      (Matrix.of fun i j => P.pairing (r i) (s j)).det := by
  classical
  choose f _ _ hf using fun i => b.exists_root_eq_sum_int (r i)
  choose g _ _ hg using fun j => b.flip.exists_root_eq_sum_int (s j)
  have hroot (i : Fin n) :
      P.root (r i) = ∑ a : Fin n, f i (e.symm a).val • P.root (e.symm a).val := by
    rw [hf i, Finset.sum_subtype b.support (fun _ => Iff.rfl)]
    exact (Equiv.sum_comp e.symm (fun a : b.support => f i a.val • P.root a.val)).symm
  have hcoroot (j : Fin n) :
      P.coroot (s j) = ∑ a : Fin n, g j (e.symm a).val • P.coroot (e.symm a).val := by
    change P.flip.root (s j) = _
    rw [hg j, Finset.sum_subtype b.flip.support (fun _ => Iff.rfl)]
    exact (Equiv.sum_comp e.symm (fun a : b.support => g j a.val • P.coroot a.val)).symm
  let A : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => f i (e.symm j).val
  let C : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => P.pairing (e.symm i).val (e.symm j).val
  let B : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => g j (e.symm i).val
  have hpair : (Matrix.of fun i j => P.pairing (r i) (s j)) = A * C * B := by
    ext i j
    change P.toLinearMap (P.root (r i)) (P.coroot (s j)) = _
    rw [hroot, hcoroot]
    simp only [Matrix.mul_apply, A, B, C, Matrix.of_apply, map_sum, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RootPairing.root_coroot_eq_pairing]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact mul_comm _ _
  rw [hpair, Matrix.det_mul, Matrix.det_mul]
  exact ⟨A.det * B.det, by change _ = C.det * _; ring⟩

/-- A based integral root pairing of type D5 has no five roots with the
restricted pairing matrix of type A5. -/
def CartanD5ExcludesA5Statement : Prop :=
  ∀ (J X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
      (P : RootPairing J ℤ X Y) (b : P.Base) (e : b.support ≃ Fin 5),
    (∀ i j, P.pairing (e.symm i).val (e.symm j).val = CartanMatrix.D 5 i j) →
    ∀ r : Fin 5 → J, ¬ ∀ i j, P.pairing (r i) (r j) = CartanMatrix.A 5 i j

theorem cartanD5ExcludesA5 : CartanD5ExcludesA5Statement := by
  intro J X Y _ _ P b e hD r hA
  have hD' : (Matrix.of fun i j => P.pairing (e.symm i).val (e.symm j).val) = CartanMatrix.D 5 :=
    Matrix.ext hD
  have hA' : (Matrix.of fun i j => P.pairing (r i) (r j)) = CartanMatrix.A 5 := Matrix.ext hA
  have h := det_simplePairing_dvd_det_pairing b e r r
  rw [hD', hA', cartan_D_det (by decide), cartan_A_det] at h
  norm_num at h

end Langlands.LinearAlgebra

import Langlands.Algebra.ReducedNormFiniteChart
import Langlands.GroupScheme.Quaternionic.KneserThreeQuaternion

/-! # Pure quaternion norms over a split coefficient field -/

noncomputable section

open Matrix
open scoped TensorProduct

universe u

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

variable {F D R : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]
  [Invertible (2 : R)]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)
  (e : R ⊗[F] D ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)

include e in
/-- Over a split coefficient field the pure quaternion norm represents every scalar. -/
theorem exists_alternating_reducedNorm_of_split (a : R) :
    let τ := (σ.quaternionConjugation hdim hsym).baseChange R
    ∃ x : R ⊗[F] D, x ∈ τ.alternatingSubspace ∧ reducedNorm F D R x = a := by
  dsimp only
  let τ := (σ.quaternionConjugation hdim hsym).baseChange R
  by_cases ha : a = 0
  · subst a
    exact ⟨0, Submodule.zero_mem _, _root_.map_zero _⟩
  let M : Matrix (Fin 2) (Fin 2) R := !![0, 1; -a, 0]
  let x := e.symm M
  have he : e x = M := e.apply_symm_apply M
  have hd : M.det = a := by simp [M, Matrix.det_fin_two]
  have hnorm : reducedNorm F D R x = a := by
    rw [reducedNorm_eq_chart_det_fintype F D e, he, hd]
  have hmul : M * M = algebraMap R (Matrix (Fin 2) (Fin 2) R) (-a) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply]
  have hx2 : x * x = algebraMap R (R ⊗[F] D) (-a) := by
    apply e.injective
    rw [_root_.map_mul, he, AlgEquiv.commutes, hmul]
  have hnormproduct : x * τ x = algebraMap R (R ⊗[F] D) a := by
    change x * (σ.quaternionConjugation hdim hsym).baseChange R x = _
    rw [σ.quaternionConjugation_norm_baseChange hdim hsym, hnorm]
  have hzero : x * (τ x + x) = x * 0 := by
    rw [mul_add, hnormproduct, hx2, ← _root_.map_add, add_neg_cancel, _root_.map_zero, mul_zero]
  have hx : IsUnit x := ((Matrix.isUnit_iff_isUnit_det M).mpr (hd ▸ isUnit_iff_ne_zero.mpr ha)).map
    e.symm.toMonoidHom
  have hneg : τ x = -x := eq_neg_of_add_eq_zero_left (hx.mul_left_cancel hzero)
  refine ⟨x, ?_, hnorm⟩
  exact KneserThree.mem_alternatingSubspace_of_neg τ (h := ⅟ (2 : R)) (mul_invOf_self _) hneg

/-- A splitting chart realizes every scalar as the reduced norm of a pure quaternion. -/
def SplitPureNormStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R] [Invertible (2 : R)]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3),
    Nonempty (R ⊗[F] D ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) →
    ∀ a : R, ∃ x : R ⊗[F] D, x ∈ ((σ.quaternionConjugation hdim hsym).baseChange R).alternatingSubspace ∧
      reducedNorm F D R x = a

theorem splitPureNorm : SplitPureNormStatement.{u} := by
  intro F D R _ _ _ _ _ _ _ _ _ σ hdim hsym ⟨e⟩ a
  exact σ.exists_alternating_reducedNorm_of_split hdim hsym e a

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

import Langlands.GroupScheme.Examples.QuasiSplitUnitaryNonCommutativeStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic
import Mathlib.RingTheory.Flat.Basic

/-! # Noncommuting rational points of the hyperbolic unitary group -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The antidiagonal matrix and a nonzero upper root element do not commute. -/
theorem nonCommutative : NonCommutativeStatement.{u} := by
  classical
  intro F E _ _ _ _ κ _ b c hc
  obtain ⟨t, ht⟩ : ∃ t : E, c t ≠ t := by
    by_contra! h
    apply hc
    ext t
    exact h t
  let T : Over (Spec (CommRingCat.of F)) := Over.mk (𝟙 _)
  let R := ((algΓ (CommRingCat.of F)).obj T).unop
  let : Nontrivial R :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  let x : E ⊗[F] R := (t - c t) ⊗ₜ[F] (1 : R)
  have hx : x ≠ 0 := by
    intro h
    have hinj := Algebra.TensorProduct.includeLeft_injective
      (R := F) (S := F) (A := E) (B := R) (algebraMap F R).injective
    have he : t - c t = 0 := hinj (by simpa [x] using h)
    exact ht (sub_eq_zero.mp he).symm
  have hxtrace : x ∈ traceZero R c := by
    rw [mem_traceZero]
    simp only [x, scalarConjugation_tmul, map_sub, conjugation_involutive c t,
      TensorProduct.sub_tmul]
    abel
  have hJ : gram (E ⊗[F] R) * gram (E ⊗[F] R) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gram, Matrix.mul_apply, Fin.sum_univ_two]
  let j : GL (Fin 2) (E ⊗[F] R) :=
    { val := gram _
      inv := gram _
      val_inv := hJ
      inv_val := hJ }
  have hj : j ∈ matrixPoints R c := by
    rw [matrixPoints, Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
    ext i j'
    fin_cases i <;> fin_cases j' <;>
      simp [j, gram, matrixInvolution, adjoint, Matrix.mul_apply, Fin.sum_univ_two]
  let g : matrixPoints R c := ⟨j, hj⟩
  let h : matrixPoints R c := upperRoot R c (Multiplicative.ofAdd ⟨x, hxtrace⟩)
  refine ⟨(pointsEquiv b c T).symm g, (pointsEquiv b c T).symm h, ?_⟩
  intro heq
  have hm : g * h = h * g := by
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      congrArg (pointsEquiv b c T) heq
  have hentry := congrArg
    (fun z : matrixPoints R c => (z.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 0 0) hm
  have hzero : 0 = x := by
    simpa [g, h, j, gram, upperRoot, upperRootMatrix, Matrix.mul_apply,
      Fin.sum_univ_two] using hentry
  exact hx hzero.symm

end Langlands.GroupScheme.QuasiSplitUnitary

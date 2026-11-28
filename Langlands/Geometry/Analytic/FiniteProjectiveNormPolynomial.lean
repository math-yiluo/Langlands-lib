import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.TensorProduct.Free

/-! # A norm polynomial of a finite projective algebra -/

noncomputable section

namespace Langlands.Analytic

open MvPolynomial Matrix LinearMap
open scoped TensorProduct

/-- The norm polynomial of a linear combination in a finite projective algebra
specializes to the product of the corresponding linear forms over any splitting
of the algebra. The rank may vary on the base. -/
theorem exists_normPolynomial {R S σ : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S] [Module.Projective R S] [Fintype σ] (b : σ → S) :
    ∃ P : MvPolynomial σ R,
      ∀ (L : Type*) [CommRing L] [Algebra R L] (ι : Type*) [Fintype ι]
        (e : L ⊗[R] S ≃ₐ[L] (ι → L)),
        MvPolynomial.map (algebraMap R L) P =
          ∏ j : ι, ∑ i : σ, C (e (1 ⊗ₜ[R] b i) j) * X i := by
  classical
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' R S
  obtain ⟨s, hrs⟩ := r.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hr)
  let U := Pi.basisFun R (Fin n)
  let M (i : σ) := toMatrix U U (s.comp ((Algebra.lmul R S (b i)).comp r))
  let J := toMatrix U U (s.comp r)
  let P : MvPolynomial σ R :=
    Matrix.det (1 + ((∑ i : σ, (X i : MvPolynomial σ R) • (M i).map
      (C : R →+* MvPolynomial σ R)) - J.map (C : R →+* MvPolynomial σ R)))
  refine ⟨P, ?_⟩
  intro L _ _ ι _ e
  let U' := Algebra.TensorProduct.basis L U
  let V := (Pi.basisFun L ι).map e.symm.toLinearEquiv
  let C' : L →+* MvPolynomial σ L := C
  let A : Matrix (Fin n) ι (MvPolynomial σ L) :=
    (toMatrix V U' (s.baseChange L)).map C'
  let B : Matrix ι (Fin n) (MvPolynomial σ L) :=
    (toMatrix U' V (r.baseChange L)).map C'
  let D (i : σ) : Matrix ι ι (MvPolynomial σ L) :=
    (toMatrix V V ((Algebra.lmul R S (b i)).baseChange L)).map C'
  let Q : Matrix ι ι (MvPolynomial σ L) := ∑ i : σ, (X i : MvPolynomial σ L) • D i
  have hBA : B * A = 1 := by
    dsimp only [A, B]
    rw [← Matrix.map_mul (f := C'), ← toMatrix_comp V U' V, ← baseChange_comp,
      hrs, baseChange_id, toMatrix_id, Matrix.map_one C' (map_zero _) (map_one _)]
  have hC (N : Matrix (Fin n) (Fin n) R) :
      (N.map (C : R →+* MvPolynomial σ R)).map
          (MvPolynomial.map (algebraMap R L)) = (N.map (algebraMap R L)).map C' := by
    apply Matrix.ext
    intro j k
    simp only [Matrix.map_apply, map_C, C']
  have hM (i : σ) :
      ((M i).map C).map (MvPolynomial.map (algebraMap R L)) = A * D i * B := by
    rw [hC]
    dsimp only [M, A, D, B]
    rw [← toMatrix_baseChange, baseChange_comp, baseChange_comp,
      toMatrix_comp U' V U', toMatrix_comp U' V V,
      Matrix.map_mul (f := C'), Matrix.map_mul (f := C'), Matrix.mul_assoc]
  have hJ : (J.map C).map (MvPolynomial.map (algebraMap R L)) = A * B := by
    rw [hC]
    dsimp only [J, A, B]
    rw [← toMatrix_baseChange, baseChange_comp, toMatrix_comp U' V U',
      Matrix.map_mul (f := C')]
  have hmap : MvPolynomial.map (algebraMap R L) P =
      Matrix.det (1 + A * (Q - 1) * B) := by
    dsimp only [P]
    rw [RingHom.map_det]
    apply congrArg Matrix.det
    let φ : Matrix (Fin n) (Fin n) (MvPolynomial σ R) →+*
        Matrix (Fin n) (Fin n) (MvPolynomial σ L) :=
      (MvPolynomial.map (algebraMap R L)).mapMatrix
    change φ (1 + ((∑ i : σ, X i • (M i).map C) - J.map C)) = _
    rw [map_add, map_one, map_sub, map_sum]
    have hterm (i : σ) : φ ((X i : MvPolynomial σ R) • (M i).map C) =
        (X i : MvPolynomial σ L) • (A * D i * B) := by
      apply Matrix.ext
      intro j k
      rw [← hM i]
      simp only [φ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
        smul_eq_mul, map_mul, map_X]
    simp_rw [hterm]
    change 1 + ((∑ i : σ, (X i : MvPolynomial σ L) • (A * D i * B)) -
      (J.map C).map (MvPolynomial.map (algebraMap R L))) = _
    rw [hJ]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    simp only [Q, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hD (i : σ) : D i = Matrix.diagonal (fun j => C (e (1 ⊗ₜ[R] b i) j)) := by
    apply Matrix.ext
    intro j k
    dsimp only [D]
    rw [Algebra.baseChange_lmul]
    simp only [Matrix.map_apply, toMatrix_apply, V, Module.Basis.map_repr,
      Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      ← AlgEquiv.toLinearEquiv_symm, AlgEquiv.symm_symm, LinearEquiv.trans_apply,
      Pi.basisFun_repr, Pi.basisFun_apply, C']
    change (C (e ((1 ⊗ₜ[R] b i) * e.symm (Pi.single k 1)) j) :
      MvPolynomial σ L) = _
    rw [map_mul, e.apply_symm_apply]
    by_cases hjk : j = k
    · subst k
      simp
    · simp [Matrix.diagonal_apply_ne _ hjk, Pi.single_eq_of_ne hjk]
  rw [hmap, Matrix.det_one_add_mul_comm (A * (Q - 1)) B,
    ← Matrix.mul_assoc, hBA, Matrix.one_mul, add_sub_cancel]
  have hQ : Q = Matrix.diagonal (fun j => ∑ i : σ, C (e (1 ⊗ₜ[R] b i) j) * X i) := by
    dsimp only [Q]
    simp_rw [hD, ← Matrix.diagonal_smul]
    apply Matrix.ext
    intro j k
    by_cases hjk : j = k
    · subst k
      simp [Matrix.sum_apply, mul_comm]
    · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ hjk]
  rw [hQ, Matrix.det_diagonal]

end Langlands.Analytic

import Langlands.LinearAlgebra.MatrixAEvalConjugacyProof
import Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Matrix conjugacy in a squarefree characteristic-polynomial fiber -/

noncomputable section

namespace Langlands

open Polynomial

variable {F : Type*} [Field F]

private lemma charpoly_piMap (m : ℕ) (M : Fin m → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)] [∀ i, FiniteDimensional F (M i)]
    (f : ∀ i, M i →ₗ[F] M i) :
    (LinearMap.piMap f).charpoly = ∏ i, (f i).charpoly := by
  classical
  induction m with
  | zero =>
      have : Subsingleton (∀ i : Fin 0, M i) :=
        ⟨fun _ _ => funext fun i => Fin.elim0 i⟩
      have hzero : LinearMap.piMap f = 0 := Subsingleton.elim _ _
      simp [hzero, Module.finrank_zero_of_subsingleton]
  | succ m ih =>
      let e : (∀ i, M i) ≃ₗ[F] M 0 × (∀ i : Fin m, M i.succ) :=
        { (Fin.consEquiv M).symm with
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hconj : e.conj (LinearMap.piMap f) =
          (f 0).prodMap (LinearMap.piMap fun i : Fin m => f i.succ) := by
        apply LinearMap.ext
        intro x
        apply Prod.ext
        · change f 0 (Fin.cons x.1 x.2 0) = f 0 x.1
          rw [Fin.cons_zero]
        · funext i
          change f i.succ (Fin.cons x.1 x.2 i.succ) = f i.succ (x.2 i)
          rw [Fin.cons_succ]
      rw [← e.charpoly_conj, hconj, LinearMap.charpoly_prodMap, ih, Fin.prod_univ_succ]

private lemma charpoly_adjoinRoot_lmul {q : F[X]} (hq : q.Monic)
    [FiniteDimensional F (AdjoinRoot q)] :
    (Algebra.lmul F (AdjoinRoot q) (AdjoinRoot.root q)).charpoly = q := by
  let pb := AdjoinRoot.powerBasis hq.ne_zero
  rw [← LinearMap.charpoly_toMatrix _ pb.basis]
  change (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = q
  rw [charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen_of_monic hq]

private lemma charpoly_eq_prod_of_polynomialModule_equiv {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (q : Fin m → F[X]) (hq : ∀ i, (q i).Monic)
    (e : Module.AEval' A.mulVecLin ≃ₗ[F[X]] (∀ i, F[X] ⧸ Ideal.span {q i})) :
    A.charpoly = ∏ i, q i := by
  classical
  let V (i : Fin m) := AdjoinRoot (q i)
  have : ∀ i, FiniteDimensional F (V i) :=
    fun i => (AdjoinRoot.powerBasis (hq i).ne_zero).finite
  let eF : (Fin n → F) ≃ₗ[F] (∀ i, V i) :=
    (Module.AEval'.of A.mulVecLin).trans (e.restrictScalars F)
  let L (i : Fin m) : V i →ₗ[F] V i := Algebra.lmul F (V i) (AdjoinRoot.root (q i))
  have hconj : eF.conj A.mulVecLin = LinearMap.piMap L := by
    apply LinearMap.ext
    intro v
    funext i
    rw [LinearEquiv.conj_apply_apply]
    change e (Module.AEval'.of A.mulVecLin (A.mulVecLin (eF.symm v))) i = _
    rw [← Module.AEval'.X_smul_of, e.map_smul]
    have hv : e (Module.AEval'.of A.mulVecLin (eF.symm v)) = v := eF.apply_symm_apply v
    rw [hv]
    rfl
  rw [← Matrix.charpoly_mulVecLin, ← eF.charpoly_conj, hconj, charpoly_piMap]
  exact Finset.prod_congr rfl fun i _ => charpoly_adjoinRoot_lmul (hq i)

private def quotientProductEquiv {m : ℕ} (q : Fin m → F[X])
    (hsq : Squarefree (∏ i, q i)) :
    (F[X] ⧸ Ideal.span {∏ i, q i}) ≃ₗ[F[X]] (∀ i, F[X] ⧸ Ideal.span {q i}) := by
  classical
  let I (i : Fin m) : Ideal F[X] := Ideal.span {q i}
  have hCoprime : Pairwise (fun i j => IsCoprime (I i) (I j)) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).2
    have hdiv : q i * q j ∣ ∏ k, q k := by
      rw [← Finset.prod_pair hij]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)
    exact (IsRelPrime.of_squarefree_mul (hsq.squarefree_of_dvd hdiv)).isCoprime
  have hI : Ideal.span {∏ i, q i} = ⨅ i, I i := by
    rw [← Ideal.prod_span_singleton,
      Ideal.prod_eq_iInf_of_pairwise_isCoprime
        (s := Finset.univ) (fun i _ j _ hij => hCoprime hij)]
    simp
  let e : (F[X] ⧸ ⨅ i, I i) ≃ₐ[F[X]] (∀ i, F[X] ⧸ I i) :=
    { Ideal.quotientInfRingEquivPiQuotient I hCoprime with
      commutes' := fun _ => rfl }
  exact (Ideal.quotientEquivAlgOfEq F[X] hI).toLinearEquiv.trans e.toLinearEquiv

private lemma polynomialModule_equiv_quotient_of_squarefree_charpoly {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hsq : Squarefree A.charpoly) :
    Nonempty (Module.AEval' A.mulVecLin ≃ₗ[F[X]] (F[X] ⧸ Ideal.span {A.charpoly})) := by
  have hann : aeval A.mulVecLin A.charpoly = 0 := by
    rw [← Matrix.charpoly_mulVecLin]
    exact LinearMap.aeval_self_charpoly _
  obtain ⟨m, q, -, hq, ⟨e⟩⟩ := polynomialModuleBoundedCyclicDecomposition
    F (Fin n → F) A.mulVecLin A.charpoly A.charpoly_monic.ne_zero hann
  have hprod := charpoly_eq_prod_of_polynomialModule_equiv A q (fun i => (hq i).1) e
  have eQ : (F[X] ⧸ Ideal.span {A.charpoly}) ≃ₗ[F[X]] (∀ i, F[X] ⧸ Ideal.span {q i}) := by
    rw [hprod]
    exact quotientProductEquiv q (hprod ▸ hsq)
  exact ⟨e.trans eQ.symm⟩

/-- Over a field, a squarefree characteristic polynomial determines a matrix
up to conjugation by a unit. -/
theorem matrixConj_of_squarefree_charpoly_eq {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hsq : Squarefree A.charpoly) (hAB : A.charpoly = B.charpoly) :
    ∃ g : Matrix.GeneralLinearGroup (Fin n) F,
      (g : Matrix (Fin n) (Fin n) F) * A *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) = B := by
  obtain ⟨eA⟩ := polynomialModule_equiv_quotient_of_squarefree_charpoly A hsq
  obtain ⟨eB⟩ := polynomialModule_equiv_quotient_of_squarefree_charpoly B (hAB ▸ hsq)
  have e : Module.AEval' B.mulVecLin ≃ₗ[F[X]] (F[X] ⧸ Ideal.span {A.charpoly}) := by
    rw [hAB]
    exact eB
  exact matrixAEvalConjugacy F n A B (eA.trans e.symm)

end Langlands

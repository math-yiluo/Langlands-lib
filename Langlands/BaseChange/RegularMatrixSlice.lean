import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Commutator and polynomial directions at a regular matrix

The commutator directions and the first `n` powers of a matrix with separable characteristic
polynomial span the matrix space. This supplies the linear algebra for local conjugation.
-/

noncomputable section

open Matrix Polynomial

namespace Langlands.BaseChange

private theorem exists_diagonalizing_algEquiv {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : A.charpoly.Separable) :
    ∃ (e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K)
      (d : Fin n → K), Function.Injective d ∧ e A = diagonal d := by
  classical
  let s := A.charpoly.roots.toFinset
  have hs : s.card = n := by
    dsimp [s]
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hA),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e := (Finset.equivFinOfCardEq hs).symm
  let d : Fin n → K := fun i => (e i).val
  have hd : Function.Injective d := Subtype.val_injective.comp e.injective
  let f : Module.End K (Fin n → K) := Matrix.toLinAlgEquiv' A
  have hroot (i : Fin n) : IsRoot A.charpoly (d i) :=
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp (e i).property)
  have hev (i : Fin n) : f.HasEigenvalue (d i) := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    change d i ∈ spectrum K A.toLin'
    rw [Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (hroot i)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli := f.eigenvectors_linearIndependent' d hd v hv
  let b := basisOfLinearIndependentOfCardEqFinrank' v hli
    (by rw [Module.finrank_fintype_fun_eq_card])
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' ..
  refine ⟨Matrix.toLinAlgEquiv'.trans (LinearMap.toMatrixAlgEquiv b), d, hd, ?_⟩
  ext i j
  change LinearMap.toMatrixAlgEquiv b f i j = diagonal d i j
  have hj : f (b j) = d j • b j := by simpa only [hb] using (hv j).apply_eq_smul
  rw [LinearMap.toMatrixAlgEquiv_apply, hj, map_smul, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst j
    simp
  · simp [diagonal_apply_ne d hij, Finsupp.single_eq_of_ne hij]

private theorem exists_diagonal_commutator_add_powers {K : Type*} [Field K]
    {n : ℕ} (d : Fin n → K) (hd : Function.Injective d) (Y : Matrix (Fin n) (Fin n) K) :
    ∃ (X : Matrix (Fin n) (Fin n) K) (c : Fin n → K),
      X * diagonal d - diagonal d * X + ∑ i : Fin n, c i • (diagonal d) ^ (i : ℕ) = Y := by
  have hunit : IsUnit (vandermonde d) := (Matrix.isUnit_iff_isUnit_det (vandermonde d)).mpr
    (isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr hd))
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) Y.diag
  let X : Matrix (Fin n) (Fin n) K := fun i j => Y i j / (d j - d i)
  refine ⟨X, c, ?_⟩
  have hc' (i : Fin n) : ∑ k : Fin n, c k * d i ^ (k : ℕ) = Y i i := by
    simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, mul_comm] using congrFun hc i
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_pow]
  by_cases hij : i = j
  · subst j
    simpa [mul_comm (X i i), Pi.pow_apply, smul_eq_mul] using hc' i
  · rw [mul_comm (d i), ← mul_sub]
    simp [Matrix.diagonal_apply_ne _ hij, sub_ne_zero.mpr (ne_comm.mp (hd.ne hij)), X]

/-- A matrix with separable characteristic polynomial has enough commutator and polynomial
directions to span the full matrix space. -/
theorem exists_commutator_add_powers {F : Type*} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : A.charpoly.Separable) (Y : Matrix (Fin n) (Fin n) F) :
    ∃ (X : Matrix (Fin n) (Fin n) F) (c : Fin n → F),
      X * A - A * X + ∑ i : Fin n, c i • A ^ (i : ℕ) = Y := by
  let K := AlgebraicClosure F
  let ι := algebraMap F K
  let B := A.map ι
  have hB : B.charpoly.Separable := by
    change (A.map ι).charpoly.Separable
    rw [Matrix.charpoly_map]
    exact hA.map
  obtain ⟨e, d, hd, he⟩ := exists_diagonalizing_algEquiv B hB
  obtain ⟨Z, c, hc⟩ := exists_diagonal_commutator_add_powers d hd (e (Y.map ι))
  let X := e.symm Z
  have hX : X * B - B * X + ∑ i : Fin n, c i • B ^ (i : ℕ) = Y.map ι := by
    apply e.injective
    simpa only [X, map_add, map_sub, map_mul, map_sum, map_smul, map_pow, he,
      AlgEquiv.apply_symm_apply] using hc
  let incl := (Algebra.ofId F K).toLinearMap
  have hincl : LinearMap.ker incl = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap F K).injective
  obtain ⟨p, hp⟩ := incl.exists_leftInverse_of_injective hincl
  have hp' (a : F) : p (ι a) = a := LinearMap.congr_fun hp a
  have hmul (a : F) (z : K) : p (ι a * z) = a * p z := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  let P : Matrix (Fin n) (Fin n) K →ₗ[F] Matrix (Fin n) (Fin n) F := p.mapMatrix
  have hleft (U : Matrix (Fin n) (Fin n) F) (V : Matrix (Fin n) (Fin n) K) :
      P (U.map ι * V) = U * P V := by
    ext i j
    change p (∑ k, ι (U i k) * V k j) = ∑ k, U i k * p (V k j)
    simp only [map_sum, hmul]
  have hright (U : Matrix (Fin n) (Fin n) F) (V : Matrix (Fin n) (Fin n) K) :
      P (V * U.map ι) = P V * U := by
    ext i j
    change p (∑ k, V i k * ι (U k j)) = ∑ k, p (V i k) * U k j
    simp only [map_sum, mul_comm (V _ _), hmul, mul_comm (U _ _)]
  have hscalar (a : K) (U : Matrix (Fin n) (Fin n) F) :
      P (a • U.map ι) = p a • U := by
    ext i j
    change p (a * ι (U i j)) = p a * U i j
    rw [mul_comm a, hmul, mul_comm]
  have hpow (i : ℕ) : B ^ i = (A ^ i).map ι :=
    ((ι.mapMatrix : Matrix (Fin n) (Fin n) F →+* _).map_pow A i).symm
  have hY : P (Y.map ι) = Y := by
    ext i j
    exact hp' (Y i j)
  refine ⟨P X, fun i => p (c i), ?_⟩
  have h := congrArg P hX
  simp_rw [map_add, map_sub, map_sum, hpow, hscalar, hY] at h
  rwa [hright, hleft] at h

end Langlands.BaseChange

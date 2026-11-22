import Langlands.Galois.QuadraticFrobeniusPatchingStatement
import Langlands.Group.LieKolchin.Triangularization
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-! # Characteristic polynomials of powers -/

noncomputable section

open Polynomial
open scoped Matrix

namespace Langlands.GaloisRepresentation.QuadraticFrobeniusPatching

private theorem exists_upperTriangular_conjugate {C : Type*} [Field C] [IsAlgClosed C] :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) C),
      ∃ P Q : Matrix (Fin n) (Fin n) C, P * Q = 1 ∧ (Q * A * P).IsUpperTriangular := by
  open Langlands.Algebra.GradedHopf.Triangular Langlands.LieKolchin in
  intro n
  induction n with
  | zero =>
    intro A
    exact ⟨1, 1, Matrix.mul_one 1, fun i => i.elim0⟩
  | succ n ih =>
    intro A
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    have hAv : A *ᵥ v = c • v := by
      simpa only [Matrix.toLin'_apply] using hv.apply_eq_smul
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv.2
    let P₁ := stepP v i₀
    let Q₁ := stepQ v i₀
    have hQP : Q₁ * P₁ = 1 := stepQ_mul_stepP v i₀ hi₀
    have hPQ : P₁ * Q₁ = 1 := mul_eq_one_comm.mp hQP
    let B := Q₁ * A * P₁
    have hB0 (i : Fin n) : B i.succ 0 = 0 := by
      have hQv : Q₁ *ᵥ v = fun j => (Q₁ * P₁) j 0 := by
        ext j
        rw [mul_stepP_apply_zero]
      change (Q₁ * A * stepP v i₀) i.succ 0 = 0
      rw [mul_stepP_apply_zero, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, hQv, hQP]
      simp [Matrix.one_apply_ne (Fin.succ_ne_zero i)]
    obtain ⟨P₂, Q₂, hPQ₂, htri⟩ := ih (B.submatrix Fin.succ Fin.succ)
    refine ⟨P₁ * ext1 P₂, ext1 Q₂ * Q₁, ?_, fun i j hji => ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (ext1 P₂), ext1_mul, hPQ₂, ext1_one,
        Matrix.one_mul, hPQ]
    · have hE : ext1 Q₂ * Q₁ * A * (P₁ * ext1 P₂) = ext1 Q₂ * B * ext1 P₂ := by
        simp only [B, Matrix.mul_assoc]
      rw [hE]
      cases i using Fin.cases with
      | zero => exact absurd hji (Fin.not_lt_zero j)
      | succ i =>
        cases j using Fin.cases with
        | zero => exact ext1_mul_mul_succ_zero Q₂ P₂ B hB0 i
        | succ j =>
          rw [ext1_mul_mul_succ_succ]
          exact htri (Fin.succ_lt_succ_iff.mp hji)

private theorem charpoly_pow_of_upperTriangular {C : Type*} [Field C] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) C) (hA : A.IsUpperTriangular) (d : ℕ) :
    (A ^ d).charpoly = frobeniusRootPower d A.charpoly := by
  classical
  have hdiag (k : ℕ) (i : Fin n) : (A ^ k) i i = A i i ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i, ih, pow_succ]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with hj | hj
        · rw [hA.pow k hj, zero_mul]
        · rw [hA hj, mul_zero]
      · simp
  have hchar (B : Matrix (Fin n) (Fin n) C) (hB : B.IsUpperTriangular) :
      B.charpoly = ((Finset.univ.val.map fun i : Fin n => B i i).map
        fun a => X - Polynomial.C a).prod := by
    rw [Matrix.charpoly_of_isUpperTriangular B hB, Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [hchar (A ^ d) (hA.pow d), hchar A hA, frobeniusRootPower, roots_multiset_prod_X_sub_C]
  simp only [hdiag, Multiset.map_map, Function.comp_apply]

/-- The eigenvalues of a power, counted with algebraic multiplicity. -/
theorem charpoly_pow {C V : Type*} [Field C] [IsAlgClosed C] [AddCommGroup V] [Module C V]
    [FiniteDimensional C V] (a : Module.End C V) (d : ℕ) :
    (a ^ d).charpoly = frobeniusRootPower d a.charpoly := by
  let b := Module.finBasis C V
  let A := LinearMap.toMatrixAlgEquiv b a
  have hmatrix : (A ^ d).charpoly = frobeniusRootPower d A.charpoly := by
    obtain ⟨P, Q, hPQ, htri⟩ := exists_upperTriangular_conjugate _ A
    let B := Q * A * P
    have hpow (k : ℕ) : B ^ k = Q * A ^ k * P := by
      induction k with
      | zero => simp [mul_eq_one_comm.mp hPQ]
      | succ k ih =>
        rw [pow_succ, ih, show B = Q * A * P from rfl]
        simp only [mul_assoc]
        rw [← mul_assoc P Q, hPQ, one_mul, ← mul_assoc (A ^ k) A, ← pow_succ]
    have hchar (k : ℕ) : (B ^ k).charpoly = (A ^ k).charpoly := by
      rw [hpow, Matrix.charpoly_mul_comm (Q * A ^ k) P, ← mul_assoc, hPQ, one_mul]
    have h := charpoly_pow_of_upperTriangular B htri d
    rw [hchar, ← pow_one B, hchar, pow_one] at h
    exact h
  rw [← LinearMap.charpoly_toMatrix (a ^ d) b, ← LinearMap.charpoly_toMatrix a b]
  change ((LinearMap.toMatrixAlgEquiv b) (a ^ d)).charpoly = frobeniusRootPower d A.charpoly
  rw [map_pow]
  exact hmatrix

theorem frobeniusRootPower_mul {C : Type*} [Field C] (d e : ℕ) (P : C[X]) :
    frobeniusRootPower e (frobeniusRootPower d P) = frobeniusRootPower (d * e) P := by
  have hroots : (frobeniusRootPower d P).roots = P.roots.map (· ^ d) := by
    simpa only [frobeniusRootPower, Multiset.map_map, Function.comp_apply] using
      roots_multiset_prod_X_sub_C (P.roots.map (· ^ d))
  change ((frobeniusRootPower d P).roots.map _).prod = _
  rw [hroots, frobeniusRootPower, Multiset.map_map]
  simp only [Function.comp_apply, pow_mul]

theorem frobeniusRootPower_natDegree {C : Type*} [Field C] [IsAlgClosed C]
    (d : ℕ) (P : C[X]) : (frobeniusRootPower d P).natDegree = P.natDegree := by
  simpa only [frobeniusRootPower, Multiset.map_map, Function.comp_apply, Multiset.card_map,
    (IsAlgClosed.splits P).natDegree_eq_card_roots] using
      natDegree_multiset_prod_X_sub_C_eq_card (P.roots.map (· ^ d))

theorem eq_of_reverse_eq_of_natDegree_eq {C : Type*} [Field C] {P Q : C[X]}
    (hd : P.natDegree = Q.natDegree) (h : P.reverse = Q.reverse) : P = Q := by
  change reflect P.natDegree P = reflect Q.natDegree Q at h
  rw [← hd] at h
  simpa only [reflect_reflect] using congrArg (reflect P.natDegree) h

end Langlands.GaloisRepresentation.QuadraticFrobeniusPatching

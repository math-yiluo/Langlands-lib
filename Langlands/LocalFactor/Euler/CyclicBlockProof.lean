import Langlands.LocalFactor.Euler.Statement
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Pi

noncomputable section

namespace Langlands.LocalFactor
namespace CyclicBlock

open Matrix

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The identity minus a shift, with separate wraparound and shift scalars. -/
def pencil (A : Matrix ι ι R) (n : ℕ) (a b : R) :
    Matrix (Fin (n + 1) × ι) (Fin (n + 1) × ι) R :=
  Matrix.of fun i j => (1 : Matrix (Fin (n + 1) × ι) (Fin (n + 1) × ι) R) i j -
    (if i.1 = 0 ∧ j.1 = Fin.last n then a * A i.2 j.2 else 0) -
    (if i.1.val = j.1.val + 1 then b * (1 : Matrix ι ι R) i.2 j.2 else 0)

private def headEquiv (n : ℕ) : ι ⊕ (Fin n × ι) ≃ (Fin (n + 1) × ι) where
  toFun := Sum.elim (fun p => (0, p)) (fun i => (i.1.succ, i.2))
  invFun := fun i => Fin.cases (Sum.inl i.2) (fun j => Sum.inr (j, i.2)) i.1
  left_inv := by
    intro i
    cases i with
    | inl p => rfl
    | inr i => rcases i with ⟨j, p⟩; rfl
  right_inv := by
    rintro ⟨i, p⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem det_pencil_zero (A : Matrix ι ι R) (a b : R) :
    (pencil A 0 a b).det = (1 - a • A).det := by
  let e : ι ≃ (Fin 1 × ι) :=
    { toFun := fun p => (0, p)
      invFun := Prod.snd
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨i, p⟩; have : i = 0 := Subsingleton.elim _ _; subst i; rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  simp [pencil, Matrix.submatrix, e, Matrix.one_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]

private theorem det_pencil_succ (A : Matrix ι ι R) (n : ℕ) (a b : R) :
    (pencil A (n + 1) a b).det = (pencil A n (a * b) b).det := by
  let B : Matrix ι (Fin (n + 1) × ι) R :=
    Matrix.of fun p j => if j.1 = Fin.last n then -(a * A p j.2) else 0
  let C : Matrix (Fin (n + 1) × ι) ι R :=
    Matrix.of fun i q => if i.1 = 0 then -(b * (1 : Matrix ι ι R) i.2 q) else 0
  let D : Matrix (Fin (n + 1) × ι) (Fin (n + 1) × ι) R :=
    Matrix.of fun i j => (1 : Matrix (Fin (n + 1) × ι) (Fin (n + 1) × ι) R) i j -
      (if i.1.val = j.1.val + 1 then b * (1 : Matrix ι ι R) i.2 j.2 else 0)
  have hblocks : (pencil A (n + 1) a b).submatrix (headEquiv (n + 1))
      (headEquiv (n + 1)) = Matrix.fromBlocks 1 B C D := by
    ext i j
    cases i with
    | inl p =>
      cases j with
      | inl q =>
        simp [pencil, Matrix.submatrix, headEquiv, Matrix.one_apply]
      | inr j =>
        have hj : j.1.succ = Fin.last (n + 1) ↔ j.1 = Fin.last n := by
          rw [← Fin.succ_last, Fin.succ_inj]
        have hz : (0 : Fin (n + 1 + 1)) ≠ j.1.succ := by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_zero, Fin.val_succ] at hval
          omega
        simp [pencil, Matrix.submatrix, headEquiv, B, Matrix.one_apply, hj, hz,
          neg_ite]
    | inr i =>
      cases j with
      | inl q =>
        simp [pencil, Matrix.submatrix, headEquiv, C, Matrix.one_apply,
          neg_ite, mul_ite]
        split_ifs <;> simp_all only [ite_true, ite_false, neg_zero]
      | inr j =>
        simp [pencil, Matrix.submatrix, headEquiv, D, Matrix.one_apply,
          Fin.succ_inj, Nat.add_right_cancel_iff, Prod.ext_iff]
        rfl
  have hmul : C * B = Matrix.of fun i j =>
      if i.1 = 0 ∧ j.1 = Fin.last n then (a * b) * A i.2 j.2 else 0 := by
    ext i j
    by_cases hi : i.1 = 0 <;> by_cases hj : j.1 = Fin.last n
    · simp [Matrix.mul_apply, C, B, hi, hj, Matrix.one_apply, mul_ite,
        mul_comm, mul_left_comm]
    · simp [Matrix.mul_apply, C, B, hi, hj]
    · simp [Matrix.mul_apply, C, B, hi, hj]
    · simp [Matrix.mul_apply, C, B, hi, hj]
  have hschur : D - C * B = pencil A n (a * b) b := by
    rw [hmul]
    ext i j
    simp only [Matrix.sub_apply, D, pencil, Matrix.of_apply]
    ring
  rw [← Matrix.det_submatrix_equiv_self (headEquiv (n + 1)), hblocks,
    Matrix.det_fromBlocks_one₁₁, hschur]

/-- Eliminating the first identity block accumulates the shift scalar. -/
theorem det_pencil (A : Matrix ι ι R) (n : ℕ) (a b : R) :
    (pencil A n a b).det = (1 - (a * b ^ n) • A).det := by
  induction n generalizing a with
  | zero => simpa using det_pencil_zero A a b
  | succ n ih =>
    rw [det_pencil_succ, ih]
    congr 2
    simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]

end CyclicBlock
end Langlands.LocalFactor

namespace Langlands.LocalFactor

open Polynomial Module

universe u v w

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem eulerPolynomial_comp_eq_det {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (A : Module.End K V) (p : K[X]) :
    (eulerPolynomial A).comp p =
      Matrix.det (1 - p • (LinearMap.toMatrix b b A).map Polynomial.C) := by
  rw [eulerPolynomial_eq_det A b, ← Polynomial.coe_compRingHom_apply,
    RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change (((1 : Matrix ι ι K[X]) i j) - X * Polynomial.C
    (LinearMap.toMatrix b b A i j)).comp p =
      (1 : Matrix ι ι K[X]) i j - p * Polynomial.C (LinearMap.toMatrix b b A i j)
  rw [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.C_comp]
  by_cases h : i = j <;>
    simp only [Matrix.one_apply, h, ite_true, ite_false, Polynomial.one_comp,
      Polynomial.zero_comp]

/-- The polynomial identity for the coordinate-specified cyclic operator. -/
theorem eulerPolynomial_cyclicBlock (A : Module.End K V) (n : ℕ)
    (T : Module.End K (Fin (n + 1) → V))
    (hzero : ∀ v, T v 0 = A (v (Fin.last n)))
    (hsucc : ∀ v (i : Fin n), T v i.succ = v i.castSucc) :
    eulerPolynomial T = (eulerPolynomial A).comp (Polynomial.X ^ (n + 1)) := by
  classical
  let b := Module.finBasis K V
  let bp := (Pi.basis fun _ : Fin (n + 1) => b).reindex
    (Equiv.sigmaEquivProd (Fin (n + 1)) (Fin (Module.finrank K V)))
  have hmatzero (p : Fin (Module.finrank K V)) (j : Fin (n + 1))
      (q : Fin (Module.finrank K V)) :
      LinearMap.toMatrix bp bp T (0, p) (j, q) =
        if j = Fin.last n then LinearMap.toMatrix b b A p q else 0 := by
    by_cases hj : j = Fin.last n
    · simp [LinearMap.toMatrix_apply, bp, Basis.reindex_apply, hzero, hj]
    · simp [LinearMap.toMatrix_apply, bp, Basis.reindex_apply, hzero, hj]
  have hmatsucc (i : Fin n) (p : Fin (Module.finrank K V)) (j : Fin (n + 1))
      (q : Fin (Module.finrank K V)) :
      LinearMap.toMatrix bp bp T (i.succ, p) (j, q) =
        if j = i.castSucc then (1 : Matrix _ _ K) p q else 0 := by
    by_cases hj : j = i.castSucc
    · simp [LinearMap.toMatrix_apply, bp, Basis.reindex_apply, hsucc, hj,
        Matrix.one_apply, Finsupp.single_apply, eq_comm]
    · simp [LinearMap.toMatrix_apply, bp, Basis.reindex_apply, hsucc, hj]
  have hpencil : (1 - (X : K[X]) • (LinearMap.toMatrix bp bp T).map Polynomial.C) =
      CyclicBlock.pencil ((LinearMap.toMatrix b b A).map Polynomial.C) n X X := by
    ext ⟨i, p⟩ ⟨j, q⟩ : 2
    refine Fin.cases ?_ (fun i => ?_) i
    · by_cases hj : j = Fin.last n <;>
        simp [CyclicBlock.pencil, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          Matrix.map_apply, hmatzero, hj]
    · have hij : i.val = j.val ↔ j = i.castSucc := by
        simp only [Fin.ext_iff, Fin.val_castSucc]
        exact eq_comm
      by_cases hj : j = i.castSucc <;> by_cases hpq : p = q <;>
        simp [CyclicBlock.pencil, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
          Matrix.map_apply, hmatsucc, hij, Matrix.one_apply, hj, hpq]
  rw [eulerPolynomial_eq_det T bp, hpencil, CyclicBlock.det_pencil,
    eulerPolynomial_comp_eq_det b A]
  congr 2
  simp [pow_succ, mul_comm]

/-- All three cyclic-block identities, with the original field and carrier universes. -/
theorem eulerCyclicBlock : EulerCyclicBlockStatement.{u, v} := by
  intro K _ V _ _ _ A n T hzero hsucc
  have hpoly := eulerPolynomial_cyclicBlock A n T hzero hsucc
  have heval (x : K) : (eulerPolynomial T).eval x =
      (eulerPolynomial A).eval (x ^ (n + 1)) := by
    rw [hpoly, Polynomial.eval_comp]
    simp
  refine ⟨hpoly, heval, ?_⟩
  intro x hT hA
  apply Units.ext
  change ((eulerPolynomial T).eval x)⁻¹ =
    ((eulerPolynomial A).eval (x ^ (n + 1)))⁻¹
  rw [heval]

end Langlands.LocalFactor

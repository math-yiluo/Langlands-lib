/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
public import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.TensorProduct.Opposite
import Mathlib.RingTheory.MatrixAlgebra

/-!
# Explicit tensor lifts for an opposite factor

Source: Stacks Project, Tag 03R7, tensor computation.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct Kronecker

/-- Inverse transpose on invertible matrices, constructed using the unit inverse. -/
def matrixInverseTranspose {R : Type*} [CommRing R] {n : Type*}
    [Fintype n] [DecidableEq n] :
    Matrix.GeneralLinearGroup n R →* Matrix.GeneralLinearGroup n R where
  toFun a :=
    { val := (a⁻¹).val.transpose
      inv := a.val.transpose
      val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one] }
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp [Matrix.transpose_mul])

/-- Kronecker product with the inverse transpose of the second factor, reindexed. -/
def tensorOppositeMatrixLift {R : Type*} [CommRing R] {n m : ℕ}
    (a : Matrix.GeneralLinearGroup (Fin n) R)
    (b : Matrix.GeneralLinearGroup (Fin m) R) :
    Matrix.GeneralLinearGroup (Fin (n * m)) R :=
  Units.map (Matrix.reindexRingEquiv R finProdFinEquiv).toMonoidHom
    (a.kronecker (matrixInverseTranspose b))

/-- The matrix lift respects coefficient maps, multiplication, and scalar matrices.

These are the elementary matrix identities used in the tensor-lift construction.
Source: Mathlib matrix Kronecker and reindexing identities.
(blueprint: lem-sc-tensor-opposite-matrix-properties). -/
theorem tensorOppositeMatrixLift_properties {R S : Type*} [CommRing R] [CommRing S]
    {n m : ℕ} (f : R →+* S)
    (a a' : Matrix.GeneralLinearGroup (Fin n) R)
    (b b' : Matrix.GeneralLinearGroup (Fin m) R) (c d : Rˣ) :
    tensorOppositeMatrixLift (Matrix.GeneralLinearGroup.map f a)
        (Matrix.GeneralLinearGroup.map f b) =
      Matrix.GeneralLinearGroup.map f (tensorOppositeMatrixLift a b) ∧
    tensorOppositeMatrixLift (a * a') (b * b') =
      tensorOppositeMatrixLift a b * tensorOppositeMatrixLift a' b' ∧
    tensorOppositeMatrixLift (Matrix.GeneralLinearGroup.scalar (Fin n) c)
        (Matrix.GeneralLinearGroup.scalar (Fin m) d) =
      Matrix.GeneralLinearGroup.scalar (Fin (n * m)) (c / d) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Units.ext
    change Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((Matrix.GeneralLinearGroup.map f a).val ⊗ₖ
          ((Matrix.GeneralLinearGroup.map f b)⁻¹).val.transpose) =
      (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (a.val ⊗ₖ (b⁻¹).val.transpose)).map f
    rw [← map_inv]
    ext i j
    simp [Matrix.GeneralLinearGroup.map, Matrix.reindex, Matrix.kroneckerMap,
      Matrix.transpose]
  · apply Units.ext
    simp [tensorOppositeMatrixLift, Matrix.GeneralLinearGroup.kronecker,
      ← Matrix.mul_kronecker_mul]
  · apply Units.ext
    change Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((Matrix.GeneralLinearGroup.scalar (Fin n) c).val ⊗ₖ
          ((Matrix.GeneralLinearGroup.scalar (Fin m) d)⁻¹).val.transpose) =
      (Matrix.GeneralLinearGroup.scalar (Fin (n * m)) (c / d)).val
    rw [← map_inv]
    change Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.diagonal (fun _ => c.val) ⊗ₖ
          (Matrix.diagonal (fun _ => (d⁻¹).val)).transpose) =
      Matrix.diagonal (fun _ => (c / d).val)
    ext i j
    change (if i.divNat = j.divNat then c.val else 0) *
        (if j.modNat = i.modNat then (d⁻¹).val else 0) =
      if i = j then (c / d).val else 0
    have hij : i.divNat = j.divNat → i.modNat = j.modNat → i = j := by
      intro h₁ h₂
      exact finProdFinEquiv.symm.injective (Prod.ext h₁ h₂)
    simp only [div_eq_mul_inv, Units.val_mul]
    split_ifs <;> simp_all

/-- Scalar extension distributes over the tensor product of algebras.
Upgrade Mathlib's linear equivalence by checking one and multiplication on pure tensors. -/
private def tensorBaseChangeEquiv (K S A B : Type*) [CommRing K] [CommRing S]
    [Ring A] [Ring B] [Algebra K S] [Algebra K A] [Algebra K B] :
    S ⊗[K] (A ⊗[K] B) ≃ₐ[S] (S ⊗[K] A) ⊗[S] (S ⊗[K] B) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.AlgebraTensorModule.distribBaseChange K S A B)
    (by simp [Algebra.TensorProduct.one_def,
      TensorProduct.AlgebraTensorModule.distribBaseChange_tmul])
    (by
      intro x y
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp [hx, hy, add_mul]
      | tmul s x =>
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add, add_mul]
        | tmul a b =>
          induction y using TensorProduct.inductionOn with
          | add x y hx hy => simp [hx, hy, mul_add]
          | tmul t y =>
            induction y using TensorProduct.inductionOn with
            | add x y hx hy =>
                simp only [TensorProduct.tmul_add, mul_add, map_add, hx, hy]
            | tmul c d =>
              simp [Algebra.TensorProduct.tmul_mul_tmul,
                TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
                mul_comm s t])

/-- The tensor/opposite splitting has the conjugation datum of the explicit tensor lifts.

Proof: commute scalar extension with the tensor product and with opposite algebras.
Apply the two given matrix splittings, transpose the opposite of the second matrix
algebra, and apply the Kronecker algebra equivalence. Reindex the product of the two
finite index sets using finProdFinEquiv. On a pure tensor the coefficient action on
its image is the Kronecker product of the coefficient actions on its two factors.
Use the two conjugation hypotheses. Transposition reverses the second conjugation,
so that its conjugator is the inverse transpose of the second lift. The Kronecker
multiplication formula gives precisely conjugation by tensorOppositeMatrixLift.
Extend from pure tensors by additivity and scalar linearity; coefficient automorphisms
fix the base field, so this extension respects the tensor relations.
Source: Stacks Project, Tag 03R7, tensor computation in the injectivity argument.
(blueprint: lem-sc-tensor-opposite-matrix-conjugation). -/
theorem exists_tensor_opposite_matrix_conjugation (K : Type u) [Field K]
    (A B : CSA.{u, u} K) (n m : ℕ)
    (eA : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (eB : (SeparableClosure K ⊗[K] B) ≃ₐ[SeparableClosure K]
      Matrix (Fin m) (Fin m) (SeparableClosure K))
    (a : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin m) (SeparableClosure K))
    (ha : ∀ (g : Gal(SeparableClosure K/K)) (v : A), (eA (1 ⊗ₜ[K] v)).map g =
      ((a g)⁻¹).val * eA (1 ⊗ₜ[K] v) * (a g).val)
    (hb : ∀ (g : Gal(SeparableClosure K/K)) (v : B), (eB (1 ⊗ₜ[K] v)).map g =
      ((b g)⁻¹).val * eB (1 ⊗ₜ[K] v) * (b g).val) :
    ∃ e : (SeparableClosure K ⊗[K] (A ⊗[K] Bᵐᵒᵖ)) ≃ₐ[SeparableClosure K]
        Matrix (Fin (n * m)) (Fin (n * m)) (SeparableClosure K),
      ∀ (g : Gal(SeparableClosure K/K)) (v : A ⊗[K] Bᵐᵒᵖ),
        (e (1 ⊗ₜ[K] v)).map g =
        ((tensorOppositeMatrixLift (a g) (b g))⁻¹).val *
          e (1 ⊗ₜ[K] v) * (tensorOppositeMatrixLift (a g) (b g)).val := by
  let S := SeparableClosure K
  let eO : (S ⊗[K] Bᵐᵒᵖ) ≃ₐ[S] Matrix (Fin m) (Fin m) S :=
    ((Algebra.TensorProduct.congr (AlgEquiv.toOpposite S S)
      (AlgEquiv.refl : Bᵐᵒᵖ ≃ₐ[K] Bᵐᵒᵖ)).trans
        (Algebra.TensorProduct.opAlgEquiv K S S B)).trans
      ((AlgEquiv.op eB).trans (Matrix.transposeAlgEquiv (Fin m) S S).symm)
  let e := (tensorBaseChangeEquiv K S A Bᵐᵒᵖ).trans
    ((Algebra.TensorProduct.congr eA eO).trans
      ((Matrix.kroneckerAlgEquiv (Fin n) (Fin m) S).trans
        (Matrix.reindexAlgEquiv S S finProdFinEquiv)))
  refine ⟨e, ?_⟩
  intro g v
  induction v using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [TensorProduct.tmul_add, map_add, Matrix.map_add g g.map_add,
      Matrix.mul_add, Matrix.add_mul, hx, hy]
  | tmul x y =>
    rw [← MulOpposite.op_unop y]
    change (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (eA (1 ⊗ₜ[K] x) ⊗ₖ (eB (1 ⊗ₜ[K] y.unop)).transpose)).map g =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((a g)⁻¹.val ⊗ₖ (b g).val.transpose) *
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (eA (1 ⊗ₜ[K] x) ⊗ₖ (eB (1 ⊗ₜ[K] y.unop)).transpose) *
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((a g).val ⊗ₖ (b g)⁻¹.val.transpose)
    have hmap : (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (eA (1 ⊗ₜ[K] x) ⊗ₖ (eB (1 ⊗ₜ[K] y.unop)).transpose)).map g =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((eA (1 ⊗ₜ[K] x)).map g ⊗ₖ ((eB (1 ⊗ₜ[K] y.unop)).map g).transpose) := by
      ext i j
      simp [Matrix.reindex, Matrix.kroneckerMap, Matrix.transpose]
    rw [hmap, ha, hb]
    change (Matrix.reindexRingEquiv S finProdFinEquiv) _ =
      (Matrix.reindexRingEquiv S finProdFinEquiv) _ *
        (Matrix.reindexRingEquiv S finProdFinEquiv) _ *
        (Matrix.reindexRingEquiv S finProdFinEquiv) _
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [Matrix.transpose_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_assoc]

end Field

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Matrix amplification of scalar-defect realizations

Source: Stacks Project, the scalar-defect construction preceding Tag 03R7.
(blueprint: lem-sc-brauer-scalar-defect-amplification).
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

private noncomputable def tensorMatrixLinear (K : Type u) [Field K]
    (A : CSA.{u, u} K) (n : ℕ) :
    SeparableClosure K ⊗[K] Matrix (Fin n) (Fin n) A ≃ₗ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K ⊗[K] A) :=
  (TensorProduct.piRight K (SeparableClosure K) (SeparableClosure K)
    (fun _ : Fin n ↦ Fin n → A)).trans
      (LinearEquiv.piCongrRight fun _ : Fin n ↦
        TensorProduct.piRight K (SeparableClosure K) (SeparableClosure K)
          (fun _ : Fin n ↦ A))

private theorem tensorMatrixLinear_tmul (K : Type u) [Field K]
    (A : CSA.{u, u} K) (n : ℕ) (s : SeparableClosure K)
    (a : Matrix (Fin n) (Fin n) A) :
    tensorMatrixLinear K A n (s ⊗ₜ[K] a) = fun i j ↦ s ⊗ₜ[K] a i j := rfl

private noncomputable def tensorMatrixAlgEquiv (K : Type u) [Field K]
    (A : CSA.{u, u} K) (n : ℕ) :
    SeparableClosure K ⊗[K] Matrix (Fin n) (Fin n) A ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K ⊗[K] A) :=
  AlgEquiv.ofLinearEquiv (tensorMatrixLinear K A n)
    (by
      change tensorMatrixLinear K A n (1 ⊗ₜ[K] 1) = 1
      rw [tensorMatrixLinear_tmul]
      ext i j
      simp [Matrix.one_apply, TensorProduct.tmul_ite, ← Algebra.TensorProduct.one_def])
    (by
      intro x y
      induction x using TensorProduct.inductionOn with
      | tmul s a =>
        induction y using TensorProduct.inductionOn with
        | tmul t b =>
          rw [Algebra.TensorProduct.tmul_mul_tmul]
          simp only [tensorMatrixLinear_tmul]
          ext i j
          simp [Matrix.mul_apply, TensorProduct.tmul_sum, Algebra.TensorProduct.tmul_mul_tmul]
        | add y₁ y₂ hy₁ hy₂ => simp_all [mul_add, map_add]
      | add x₁ x₂ hx₁ hx₂ => simp_all [add_mul, map_add])


private noncomputable def flatten (K : Type u) [Field K] (n d : ℕ) :
    Matrix (Fin n) (Fin n) (Matrix (Fin d) (Fin d) (SeparableClosure K)) ≃ₐ[
      SeparableClosure K] Matrix (Fin (n * d)) (Fin (n * d)) (SeparableClosure K) :=
  (Matrix.compAlgEquiv (Fin n) (Fin d) (SeparableClosure K) (SeparableClosure K)).trans
    (Matrix.reindexAlgEquiv (SeparableClosure K) (SeparableClosure K) finProdFinEquiv)

private theorem flatten_map (K : Type u) [Field K] (n d : ℕ)
    (g : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (M : Matrix (Fin n) (Fin n) (Matrix (Fin d) (Fin d) (SeparableClosure K))) :
    flatten K n d (M.map (fun N ↦ N.map g)) = (flatten K n d M).map g := rfl

private noncomputable def amplify (K : Type u) [Field K] (n d : ℕ) :
    Matrix.GeneralLinearGroup (Fin d) (SeparableClosure K) →*
      Matrix.GeneralLinearGroup (Fin (n * d)) (SeparableClosure K) :=
  Units.map (((flatten K n d).toRingHom.comp (Matrix.scalar (Fin n))).toMonoidHom)

private theorem amplify_map (K : Type u) [Field K] (n d : ℕ)
    (g : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (v : Matrix.GeneralLinearGroup (Fin d) (SeparableClosure K)) :
    amplify K n d (Matrix.GeneralLinearGroup.map g.toRingHom v) =
      Matrix.GeneralLinearGroup.map g.toRingHom (amplify K n d v) := by
  apply Units.ext
  change flatten K n d (Matrix.scalar (Fin n) (v.val.map g)) =
    (flatten K n d (Matrix.scalar (Fin n) v.val)).map g
  rw [← flatten_map]
  congr 1
  ext i j k l
  simp [Matrix.scalar, Matrix.diagonal_apply]
  split <;> simp

private theorem amplify_scalar (K : Type u) [Field K] (n d : ℕ)
    (c : (SeparableClosure K)ˣ) :
    amplify K n d (Matrix.GeneralLinearGroup.scalar (Fin d) c) =
      Matrix.GeneralLinearGroup.scalar (Fin (n * d)) c := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  change (Matrix.scalar (Fin n) (Matrix.scalar (Fin d) c.val))
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1
      (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 =
    (Matrix.scalar (Fin (n * d)) c.val) i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hp : finProdFinEquiv.symm i ≠ finProdFinEquiv.symm j :=
      fun heq ↦ hij (finProdFinEquiv.symm.injective heq)
    have hpair : ¬ ((finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 ∧
        (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2) :=
      fun heq ↦ hp (Prod.ext heq.1 heq.2)
    simp only [hij, ite_false]
    split_ifs <;> simp_all

/-- A positive matrix amplification realizes the original scalar-defect class.

Proof: unpack the realization of `A` into a positive size `d`, a splitting `e`,
a locally constant lift `b`, and its homogeneous cocycle `z`. Extend the given
isomorphism `f : C ≃ Mat_n(A)` to the separable closure, commute scalar extension
with the finite matrix algebra entry by entry, apply `e` entry by entry, and flatten
`Mat_n(Mat_d(Ks))` to `Mat_(n*d)(Ks)`. Both factors are positive, so the new size is
positive. These are explicit algebra equivalences, giving a splitting of `C`.
Replace each lift `b(g)` by the Kronecker product `I_n ⊗ b(g)`, reindexed to the
flattened matrix indices. This is invertible, with inverse `I_n ⊗ b(g)⁻¹`, and is
locally constant because it is a fixed function of `b(g)`.
For every entry of an element of `Mat_n(A)`, the original descent identity gives
its amplified identity; matrix multiplication and flattening preserve it.
The Kronecker product preserves products, entrywise Galois action, and scalar
matrices. Applying it to the original defect equation gives exactly the new
multiplication-defect equation with the same unit-valued cocycle `z`.
The homology image of `z` remains `x`. These explicit witnesses satisfy the
scalar-defect relation for `C`; no new cocycle or arbitrary algebra is chosen.

Source: Stacks Project, scalar-defect construction following Lemma 03R6 and the
well-defined Brauer-class map preceding Theorem 03R7.
(blueprint: lem-sc-brauer-scalar-defect-amplification). -/
theorem hasBrauerScalarDefect_of_matrix_algEquiv (K : Type u) [Field K]
    (A C : CSA.{u, u} K) (x : GaloisUnitsH2 K) (n : ℕ) (hn : n ≠ 0)
    (f : C ≃ₐ[K] Matrix (Fin n) (Fin n) A)
    (hx : HasBrauerScalarDefect K A x) : HasBrauerScalarDefect K C x := by
  obtain ⟨d, hd, e, b, hb, z, hz, hdesc, hdefect⟩ := hx
  let t := Algebra.TensorProduct.congr
    (AlgEquiv.refl : SeparableClosure K ≃ₐ[SeparableClosure K] SeparableClosure K) f
  let e' := ((t.trans (tensorMatrixAlgEquiv K A n)).trans e.mapMatrix).trans
    (flatten K n d)
  refine ⟨n * d, mul_ne_zero hn hd, e', fun g ↦ amplify K n d (b g),
    hb.comp (amplify K n d), z, hz, ?_, ?_⟩
  · intro g a
    have he : e' (1 ⊗ₜ[K] a) =
        flatten K n d (fun i j ↦ e (1 ⊗ₜ[K] (f a) i j)) := rfl
    rw [he]
    let M : Matrix (Fin n) (Fin n) (Matrix (Fin d) (Fin d) (SeparableClosure K)) :=
      fun i j ↦ e (1 ⊗ₜ[K] (f a) i j)
    have hM : M.map (fun N ↦ N.map g) =
        Matrix.scalar (Fin n) ((b g)⁻¹).val * M *
          Matrix.scalar (Fin n) (b g).val := by
      apply Matrix.ext
      intro i j
      simpa only [M, Matrix.map_apply, Matrix.scalar_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul] using hdesc g ((f a) i j)
    have hflat := congrArg (flatten K n d) hM
    have hinv : ((amplify K n d (b g))⁻¹).val =
        flatten K n d (Matrix.scalar (Fin n) ((b g)⁻¹).val) := by
      rw [← map_inv]
      rfl
    have hval : (amplify K n d (b g)).val =
        flatten K n d (Matrix.scalar (Fin n) (b g).val) := rfl
    rw [hinv, hval]
    simpa only [M, flatten_map, map_mul] using hflat
  · intro g h
    have hamp := congrArg (amplify K n d) (hdefect g h)
    simpa only [map_mul, amplify_map, amplify_scalar] using hamp

end Field

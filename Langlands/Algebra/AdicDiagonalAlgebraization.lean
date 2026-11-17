import Langlands.Algebra.FiniteRankDiagonal
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.Algebra.Bilinear

/-! # Algebraization from compatible diagonal coefficient systems -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.AdicDiagonalAlgebraization

attribute [local instance] Classical.propDecidable

variable {A : Type u} [CommRing A] (I : Ideal A)
variable {C : Type v} [AddCommGroup C] [Module A C] {M : Type w}

/-- Evaluate a tensor after two coefficient evaluations. -/
def tensorCoefficient {Q : Type*} [CommRing Q] [Algebra A Q]
    (g : C →ₗ[A] (M → Q)) (m k : M) : C ⊗[A] C →ₗ[A] Q :=
  TensorProduct.lift ((LinearMap.mul A Q).compl₁₂
    ((LinearMap.proj m).comp g) ((LinearMap.proj k).comp g))

@[simp] theorem tensorCoefficient_tmul {Q : Type*} [CommRing Q] [Algebra A Q]
    (g : C →ₗ[A] (M → Q)) (m k : M) (x y : C) :
    tensorCoefficient g m k (x ⊗ₜ[A] y) = g x m * g y k := rfl

/-- An inverse system of finitely supported coefficient families. -/
structure System where
  map : (n : ℕ) → C →ₗ[A] (M →₀ A ⧸ I ^ n)
  compatible : ∀ {n k : ℕ} (h : n ≤ k) (x : C) (m : M),
    Ideal.Quotient.factorPow I h (map k x m) = map n x m

namespace System

variable {I}
variable (f : System I (C := C) (M := M))

set_option backward.isDefEq.respectTransparency false in
/-- The completed scalar coefficient at one index. -/
def completedCoefficient (m : M) : C →ₗ[A] AdicCompletion I A where
  toFun x := ⟨fun n => Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _).symm) (f.map n x m),
    fun h => by
      simp only [AdicCompletion.transitionMap, Submodule.factorPow]
      simpa using congrArg (Ideal.Quotient.factor (le_of_eq (Ideal.mul_top _).symm))
        (f.compatible h x m)⟩
  map_add' x y := by
    ext n
    simp [map_add]
  map_smul' a x := by
    ext n
    change Ideal.Quotient.factor _ (f.map n (a • x) m) =
      a • Ideal.Quotient.factor _ (f.map n x m)
    rw [map_smul, Finsupp.smul_apply]
    exact (Ideal.Quotient.factorₐ A (le_of_eq (Ideal.mul_top (I ^ n)).symm)).toLinearMap.map_smul
      a (f.map n x m)

variable [IsAdicComplete I A]

/-- The pointwise adic limit of the coefficient families. -/
def coefficients : C →ₗ[A] (M → A) :=
  LinearMap.pi fun m => (AdicCompletion.ofLinearEquiv I A).symm.toLinearMap.comp
    (f.completedCoefficient m)

@[simp] theorem mk_coefficients (n : ℕ) (x : C) (m : M) :
    Ideal.Quotient.mk (I ^ n) (f.coefficients x m) = f.map n x m := by
  rw [← AdicCompletion.evalₐ_of I n]
  change AdicCompletion.evalₐ I n
    (AdicCompletion.of I A ((AdicCompletion.ofLinearEquiv I A).symm
      (f.completedCoefficient m x))) = _
  rw [AdicCompletion.of_ofLinearEquiv_symm]
  rw [← AdicCompletion.factor_eval_eq_evalₐ I _ (le_of_eq (Ideal.mul_top _))]
  change Ideal.Quotient.factor (le_of_eq (Ideal.mul_top (I ^ n)))
    (Ideal.Quotient.factor (le_of_eq (Ideal.mul_top (I ^ n)).symm) (f.map n x m)) = _
  simp

/-- Tensor coefficients commute with reduction to every adic quotient. -/
theorem mk_tensorCoefficient (n : ℕ) (t : C ⊗[A] C) (m k : M) :
    Ideal.Quotient.mk (I ^ n) (tensorCoefficient f.coefficients m k t) =
      tensorCoefficient ((Finsupp.lcoeFun (R := A)).comp (f.map n)) m k t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp only [tensorCoefficient_tmul, map_mul, mk_coefficients]; rfl
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Over the original ring, tensor coefficients are entries of the finite-rank matrix. -/
theorem tensorCoefficient_eq (t : C ⊗[A] C) (m k : M) :
    tensorCoefficient f.coefficients m k t =
      FiniteRankDiagonal.coefficients
        (TensorProduct.map f.coefficients f.coefficients t) (m, k) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp only [tensorCoefficient_tmul, TensorProduct.map_tmul,
      FiniteRankDiagonal.coefficients_tmul]
  | add t s ht hs => simp only [map_add, Pi.add_apply, ht, hs]

variable (d : C →ₗ[A] C ⊗[A] C)
variable (hd : ∀ (n : ℕ) (x : C) (m k : M),
  tensorCoefficient ((Finsupp.lcoeFun (R := A)).comp (f.map n)) m k (d x) =
    if m = k then f.map n x m else 0)

include hd in
/-- The quotient diagonal identities pass to the pointwise adic limit. -/
theorem tensorCoefficient_diagonal (x : C) (m k : M) :
    tensorCoefficient f.coefficients m k (d x) =
      if m = k then f.coefficients x m else 0 := by
  classical
  apply congrFun (IsHausdorff.funext' I
    (f := fun _ : Unit => tensorCoefficient f.coefficients m k (d x))
    (g := fun _ : Unit => if m = k then f.coefficients x m else 0) ?_) ()
  intro n _
  rw [mk_tensorCoefficient, hd]
  split_ifs <;> simp only [mk_coefficients, map_zero]

include d hd in
/-- Every limiting coefficient family has finite support over a noetherian ring. -/
theorem finite_support [IsNoetherianRing A] (x : C) :
    (Function.support (f.coefficients x)).Finite := by
  have heq : f.coefficients x = fun m =>
      FiniteRankDiagonal.coefficients
        (TensorProduct.map f.coefficients f.coefficients (d x)) (m, m) := by
    funext m
    rw [← tensorCoefficient_eq, tensorCoefficient_diagonal f d hd]
    simp
  rw [heq]
  apply FiniteRankDiagonal.finite_support_diagonal
  intro m k hmk
  rw [← tensorCoefficient_eq, tensorCoefficient_diagonal f d hd]
  simp [hmk]

/-- The algebraized linear map obtained from compatible diagonal coefficient maps. -/
def lift [IsNoetherianRing A] : C →ₗ[A] (M →₀ A) where
  toFun x := Finsupp.ofSupportFinite (f.coefficients x) (finite_support f d hd x)
  map_add' x y := by ext m; exact congrFun (f.coefficients.map_add x y) m
  map_smul' a x := by ext m; exact congrFun (f.coefficients.map_smul a x) m

@[simp] theorem lift_apply [IsNoetherianRing A] (x : C) (m : M) :
    lift f d hd x m = f.coefficients x m := rfl

@[simp] theorem mk_lift [IsNoetherianRing A] (n : ℕ) (x : C) (m : M) :
    Ideal.Quotient.mk (I ^ n) (lift f d hd x m) = f.map n x m :=
  mk_coefficients f n x m

/-- A map realizing all quotient coefficient families is unique. -/
theorem lift_unique [IsNoetherianRing A] (g : C →ₗ[A] (M →₀ A))
    (hg : ∀ (n : ℕ) (x : C) (m : M), Ideal.Quotient.mk (I ^ n) (g x m) = f.map n x m) :
    g = lift f d hd := by
  ext x m
  apply congrFun (IsHausdorff.funext' I
    (f := fun _ : Unit => g x m) (g := fun _ : Unit => lift f d hd x m) ?_) ()
  intro n _
  rw [hg, mk_lift]

end System

end Langlands.AdicDiagonalAlgebraization

import Langlands.LocalFactor.Euler.Definitions
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Structural identities for determinant Euler factors

These are theorem targets for the actual determinant polynomial and its rational
reciprocal. Exactness is imposed on the vector spaces on which the operators
act. In particular, this does not assert exactness of monodromy-kernel invariants.
-/

namespace Langlands.LocalFactor

open Polynomial
open scoped BigOperators TensorProduct

universe u v w z t

/-- A short exact sequence of finite-dimensional operator modules gives a
product of Euler polynomials and rational factors. Regularity is equivalent
to simultaneous regularity of the two factors. -/
def EulerExactSequenceStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Type w) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (U : Type z) [AddCommGroup U] [Module K U] [FiniteDimensional K U],
  ∀ (A : Module.End K V) (B : Module.End K W) (C : Module.End K U)
    (i : V →ₗ[K] W) (j : W →ₗ[K] U),
    Function.Injective i → Function.Surjective j →
    LinearMap.range i = LinearMap.ker j →
    B.comp i = i.comp A → C.comp j = j.comp B →
    eulerPolynomial B = eulerPolynomial A * eulerPolynomial C ∧
    rationalFactor B = rationalFactor A * rationalFactor C ∧
    (∀ x : K, (eulerPolynomial B).eval x ≠ 0 ↔
      (eulerPolynomial A).eval x ≠ 0 ∧ (eulerPolynomial C).eval x ≠ 0) ∧
    (∀ (x : K) (hA : (eulerPolynomial A).eval x ≠ 0)
      (hB : (eulerPolynomial B).eval x ≠ 0)
      (hC : (eulerPolynomial C).eval x ≠ 0),
      regularFactorValue B ⟨x, hB⟩ =
        regularFactorValue A ⟨x, hA⟩ * regularFactorValue C ⟨x, hC⟩)

/-- Direct-sum factorization has no extra exactness hypothesis. -/
def EulerDirectSumStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Type w) [AddCommGroup W] [Module K W] [FiniteDimensional K W],
  ∀ (A : Module.End K V) (B : Module.End K W),
    eulerPolynomial (A.prodMap B) = eulerPolynomial A * eulerPolynomial B ∧
    rationalFactor (A.prodMap B) = rationalFactor A * rationalFactor B

/-- Scaling an operator substitutes `c X` in its Euler polynomial. An invertible
operator also satisfies the reciprocal-polynomial formula away from zero. -/
def EulerScalarAndReciprocalStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  (∀ (A : Module.End K V) (c : K),
    eulerPolynomial (c • A) =
      (eulerPolynomial A).comp (Polynomial.C c * Polynomial.X)) ∧
  (∀ (A : V ≃ₗ[K] V) (x : K), x ≠ 0 →
    (eulerPolynomial A.toLinearMap).eval x =
      (-x) ^ Module.finrank K V * LinearMap.det A.toLinearMap *
        (eulerPolynomial A.symm.toLinearMap).eval x⁻¹)

/-- Removing a commuting unipotent factor leaves the Euler polynomial unchanged.
The commutation condition is essential. -/
def EulerUnipotentInvarianceStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∀ (A U : Module.End K V), Commute A U → IsNilpotent (U - 1) →
    eulerPolynomial (A * U) = eulerPolynomial A ∧
    rationalFactor (A * U) = rationalFactor A

/-- A supplied eigenbasis of the second operator gives the tensor-product
factor formula. No diagonalizability of the first operator is assumed. -/
def EulerTensorEigenbasisStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Type w) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ι : Type t) [Fintype ι],
  ∀ (A : Module.End K V) (B : Module.End K W)
    (b : Module.Basis ι K W) (β : ι → K),
    (∀ j, B (b j) = β j • b j) →
    eulerPolynomial (TensorProduct.map A B) =
      ∏ j, eulerPolynomial (β j • A) ∧
    rationalFactor (TensorProduct.map A B) =
      ∏ j, rationalFactor (β j • A)

/-- The cyclic block operator used in finite-extension induction. Its action
on every coordinate is specified, including the wraparound by `A`. -/
def EulerCyclicBlockStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
  ∀ (A : Module.End K V) (n : ℕ)
    (C : Module.End K (Fin (n + 1) → V)),
    (∀ v, C v 0 = A (v (Fin.last n))) →
    (∀ v (i : Fin n), C v i.succ = v i.castSucc) →
    eulerPolynomial C = (eulerPolynomial A).comp (Polynomial.X ^ (n + 1)) ∧
    (∀ x : K, (eulerPolynomial C).eval x =
      (eulerPolynomial A).eval (x ^ (n + 1))) ∧
    (∀ (x : K) (hC : (eulerPolynomial C).eval x ≠ 0)
      (hA : (eulerPolynomial A).eval (x ^ (n + 1)) ≠ 0),
      regularFactorValue C ⟨x, hC⟩ =
        regularFactorValue A ⟨x ^ (n + 1), hA⟩)

/-- Spectral translation is an identity of denominators and values on their
common regular domain. Here `q` is a positive real variable in a linear-algebra
lemma; an arithmetic application must instantiate the actual residue cardinality. -/
def EulerSpectralTranslationStatement : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
  ∀ (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q) (s t : ℂ),
  let c : ℂ := spectralParameter q hq t
  ((eulerPolynomial (c • A)).eval (spectralParameter q hq s : ℂ) =
    (eulerPolynomial A).eval (spectralParameter q hq (s + t) : ℂ)) ∧
  (((eulerPolynomial (c • A)).eval (spectralParameter q hq s : ℂ) ≠ 0) ↔
    (eulerPolynomial A).eval (spectralParameter q hq (s + t) : ℂ) ≠ 0) ∧
  (∀ (h₁ : (eulerPolynomial (c • A)).eval (spectralParameter q hq s : ℂ) ≠ 0)
    (h₂ : (eulerPolynomial A).eval (spectralParameter q hq (s + t) : ℂ) ≠ 0),
    spectralFactorValue (c • A) q hq ⟨s, h₁⟩ =
      spectralFactorValue A q hq ⟨s + t, h₂⟩)

/-- The coherent structural theorem family for determinant Euler factors. -/
def EulerFactorStructureStatement : Prop :=
  EulerExactSequenceStatement.{u, v, w, z} ∧
  EulerDirectSumStatement.{u, v, w} ∧
  EulerScalarAndReciprocalStatement.{u, v} ∧
  EulerUnipotentInvarianceStatement.{u, v} ∧
  EulerTensorEigenbasisStatement.{u, v, w, t} ∧
  EulerCyclicBlockStatement.{u, v} ∧
  EulerSpectralTranslationStatement.{v}

end Langlands.LocalFactor

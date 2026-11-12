import Langlands.Global.RealAlgebraSplitting
import Langlands.Shimura.Unitary.RealPositivity
import Langlands.Shimura.Unitary.Signature

/-!
# Definite signatures give positive involutions

If an involution of the second kind has the definite signature `(n, 0)` at every real place of
the totally real field `E` (`HasDefiniteSignature`), then its rational restriction becomes a
positive involution after extending scalars to `ℝ`.

* `signatureMatrix_self`, `signatureAdjoint_self_apply`: the signature `(n, 0)` adjoint is
  conjugate transposition.
* `SecondKindInvolution.definiteMatrixEquiv`: the real matrix splitting
  `ℝ ⊗_ℚ A ≃ ∏_τ M_n(ℂ)` assembled from the definite charts.
* `SecondKindInvolution.isPositive_of_hasDefiniteSignature`: positivity of
  `σ.rationalInvolution.baseChange ℝ`.
-/

noncomputable section

universe u v w z

open NumberField Module Algebra
open scoped TensorProduct

namespace Langlands.Shimura

/-- The signature matrix of signature `(n, 0)` is the identity. -/
theorem signatureMatrix_self (n : ℕ) : signatureMatrix n n = 1 := by
  ext i j
  simp [signatureMatrix, Matrix.diagonal_apply, Matrix.one_apply]

/-- The signature `(n, 0)` adjoint is conjugate transposition. -/
theorem signatureAdjoint_self_apply (n : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) :
    signatureAdjoint n n x = star x := by
  change signatureMatrix n n * star x * signatureMatrix n n = star x
  rw [signatureMatrix_self, one_mul, mul_one]

namespace SecondKindInvolution

variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {ι : Type z} [Fintype ι] (b : Basis ι E A)

/-- The real matrix splitting `ℝ ⊗_ℚ A ≃ ∏_τ M_n(ℂ)` assembled from definite charts. -/
def definiteMatrixEquiv (h : HasDefiniteSignature σ n) :
    ℝ ⊗[ℚ] A ≃ₐ[ℝ] ((E →+* ℝ) → Matrix (Fin n) (Fin n) ℂ) :=
  (Global.TotallyReal.algebraEquiv E A b).trans
    (AlgEquiv.piCongrRight fun τ => (h.2 τ).2.choose)

/-- The definite splitting carries the scalar-extended involution to conjugate transposition in
every factor. -/
theorem definiteMatrixEquiv_involution (h : HasDefiniteSignature σ n) (x : ℝ ⊗[ℚ] A) :
    definiteMatrixEquiv b h (σ.rationalInvolution.baseChange ℝ x) =
      piConjTranspose n (E →+* ℝ) (definiteMatrixEquiv b h x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    funext τ
    let : Algebra E ℝ := τ.toAlgebra
    have hc := (h.2 τ).2.choose_spec (r ⊗ₜ[E] a)
    rw [signatureAdjoint_self_apply] at hc
    simpa [definiteMatrixEquiv, piConjTranspose_apply] using hc
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Definite signatures give positivity.** If `σ` has signature `(n, 0)` at every real place,
then `σ.rationalInvolution.baseChange ℝ` is positive. -/
theorem isPositive_of_hasDefiniteSignature [Module.Finite E A] (h : HasDefiniteSignature σ n) :
    (σ.rationalInvolution.baseChange ℝ).IsPositive := by
  classical
  exact (AlgebraInvolution.isPositive_iff_of_algEquiv _ _
    (definiteMatrixEquiv (Module.finBasis E A) h)
    (definiteMatrixEquiv_involution (Module.finBasis E A) h)).2 (piConjTranspose_isPositive n _)

end SecondKindInvolution

end Langlands.Shimura

import Langlands.Shimura.Unitary.ComplexMatrixInvolution
import Langlands.Shimura.Unitary.ComplexMatrixCoefficients

noncomputable section
open Algebra Module
open scoped TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable (S : Type*) [CommRing S]

/-- Signature transpose over the coefficient ring, fixing every coefficient. -/
def signatureTransposeOver (n r : ℕ) (M : Matrix (Fin n) (Fin n) S) :
    Matrix (Fin n) (Fin n) S :=
  Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : S) else -1) *
    M.transpose * Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : S) else -1)

@[simp] theorem signatureTransposeOver_entry (n r : ℕ) (M : Matrix (Fin n) (Fin n) S)
    (i j : Fin n) :
    signatureTransposeOver S n r M i j =
      (if i.val < r then 1 else -1) * M j i * (if j.val < r then 1 else -1) := by
  simp [signatureTransposeOver, Matrix.diagonal_mul, Matrix.mul_diagonal]

@[simp] theorem signatureTransposeOver_add (n r : ℕ) (M N : Matrix (Fin n) (Fin n) S) :
    signatureTransposeOver S n r (M + N) =
      signatureTransposeOver S n r M + signatureTransposeOver S n r N := by
  simp [signatureTransposeOver, Matrix.transpose_add, mul_add, add_mul]

@[simp] theorem signatureTransposeOver_smul (n r : ℕ) (s : S)
    (M : Matrix (Fin n) (Fin n) S) :
    signatureTransposeOver S n r (s • M) = s • signatureTransposeOver S n r M := by
  ext i j
  simp only [signatureTransposeOver_entry, Matrix.smul_apply, smul_eq_mul]
  ring

variable [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- The scalar-extended real adjoint swaps factors and fixes the coefficient ring. -/
theorem scalarEquiv_adjoint (n r : ℕ) (x : S ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    scalarEquiv S n ((signatureAdjoint n r).baseChange S x) =
      (signatureTransposeOver S n r (scalarEquiv S n x).2,
       signatureTransposeOver S n r (scalarEquiv S n x).1) := by
  induction x using TensorProduct.inductionOn with
  | tmul s M =>
    simp only [AlgebraInvolution.baseChange_tmul, scalarEquiv_tmul,
      signatureTransposeOver_smul]
    apply Prod.ext <;> ext i j <;>
      simp only [Matrix.smul_apply, Matrix.map_apply, signatureAdjoint_entry,
        signatureTransposeOver_entry, star_mul, star_star, map_mul]
    all_goals split_ifs <;> simp
  | add x y hx hy =>
    simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add,
      signatureTransposeOver_add, Prod.mk_add_mk]

/-- The actual involution on the ordered pair of matrices over a complex coefficient ring. -/
def scalarSignatureInvolution (n r : ℕ) :
    AlgebraInvolution S (Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) :=
  ((signatureAdjoint n r).baseChange S).transport (scalarEquiv S n)

@[simp] theorem scalarSignatureInvolution_apply (n r : ℕ)
    (p : Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) :
    scalarSignatureInvolution S n r p =
      (signatureTransposeOver S n r p.2, signatureTransposeOver S n r p.1) := by
  rw [scalarSignatureInvolution, AlgebraInvolution.transport_apply, scalarEquiv_adjoint]
  simp

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura

variable (S : Type*) [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- The Harris involution on matrices over an arbitrary complex coefficient ring. -/
def harrisScalarMatrixInvolution (n : ℕ) (I : Type*) [DecidableEq I]
    (distinguished : I) : AlgebraInvolution S
      (I → Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) where
  linear :=
    { toFun := fun x τ => ComplexMatrix.scalarSignatureInvolution S n
        (if τ = distinguished then n - 1 else n) (x τ)
      map_add' := by intros; funext τ; exact AlgebraInvolution.apply_add _ _ _
      map_smul' := by intros; funext τ; exact AlgebraInvolution.apply_smul _ _ _ }
  map_one := by
    funext τ
    exact (ComplexMatrix.scalarSignatureInvolution S n
      (if τ = distinguished then n - 1 else n)).apply_one
  map_mul x y := by
    funext τ
    exact (ComplexMatrix.scalarSignatureInvolution S n
      (if τ = distinguished then n - 1 else n)).apply_mul (x τ) (y τ)
  involutive x := by
    funext τ
    exact (ComplexMatrix.scalarSignatureInvolution S n
      (if τ = distinguished then n - 1 else n)).apply_apply (x τ)

namespace HarrisSignatureCharts

universe u v w z
open NumberField
variable {E : Type u} {K : Type v} {A : Type w}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}
  {Φ : (E →+* ℝ) → (K →+* ℂ)}
  (C : HarrisSignatureCharts σ n Φ)
  {ι : Type z} [Fintype ι] (b : Basis ι E A)

/-- The arbitrary-coefficient matrix decomposition respects the actual involutions. -/
theorem iteratedScalarMatrixEquiv_involution (x : S ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    C.iteratedScalarMatrixEquiv b S ((σ.rationalInvolution.baseChange ℝ).baseChange S x) =
      harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished
        (C.iteratedScalarMatrixEquiv b S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
    funext τ
    change C.iteratedScalarMatrixEquiv b S
      ((σ.rationalInvolution.baseChange ℝ).baseChange S (s ⊗ₜ[ℝ] x)) τ =
      ComplexMatrix.scalarSignatureInvolution S n (if τ = C.distinguished then n - 1 else n)
        (C.iteratedScalarMatrixEquiv b S (s ⊗ₜ[ℝ] x) τ)
    simp only [AlgebraInvolution.baseChange_tmul, iteratedScalarMatrixEquiv_tmul,
      realMatrixEquiv_involution]
    change
      (s • (signatureAdjoint n (if τ = C.distinguished then n - 1 else n)
        (C.realMatrixEquiv b x τ)).map (algebraMap ℂ S),
       s • (signatureAdjoint n (if τ = C.distinguished then n - 1 else n)
        (C.realMatrixEquiv b x τ)).map (fun z => algebraMap ℂ S (star z))) =
      ComplexMatrix.scalarSignatureInvolution S n (if τ = C.distinguished then n - 1 else n)
        (s • (C.realMatrixEquiv b x τ).map (algebraMap ℂ S),
         s • (C.realMatrixEquiv b x τ).map (fun z => algebraMap ℂ S (star z)))
    simpa only [ComplexMatrix.scalarSignatureInvolution,
      AlgebraInvolution.baseChange_tmul, ComplexMatrix.scalarEquiv_tmul] using
      (AlgebraInvolution.transport_equiv
        ((signatureAdjoint n (if τ = C.distinguished then n - 1 else n)).baseChange S)
        (ComplexMatrix.scalarEquiv S n) (s ⊗ₜ[ℝ] C.realMatrixEquiv b x τ)).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Actual iterated scalar-extension similitudes in split matrix coordinates. -/
def iteratedScalarSimilitudesEquiv :
    ((σ.rationalInvolution.baseChange ℝ).baseChange S).similitudes ≃*
      (harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished).similitudes :=
  AlgebraInvolution.similitudesEquiv _ _ (C.iteratedScalarMatrixEquiv b S)
    (C.iteratedScalarMatrixEquiv_involution S b)

@[simp] theorem iteratedScalarSimilitudesEquiv_multiplier
    (g : ((σ.rationalInvolution.baseChange ℝ).baseChange S).similitudes) :
    (harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished).multiplier
      (C.iteratedScalarSimilitudesEquiv S b g) =
      ((σ.rationalInvolution.baseChange ℝ).baseChange S).multiplier g :=
  AlgebraInvolution.similitudesEquiv_multiplier _ _ _ _ g

variable [Algebra ℚ S] [IsScalarTower ℚ ℝ S]

/-- Direct rational scalar extension has the same split matrix involution. -/
theorem scalarMatrixEquiv_involution (x : S ⊗[ℚ] A) :
    C.scalarMatrixEquiv b S (σ.rationalInvolution.baseChange S x) =
      harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished
        (C.scalarMatrixEquiv b S x) := by
  simp only [scalarMatrixEquiv, AlgEquiv.trans_apply,
    AlgebraInvolution.baseChangeTowerEquiv_involution, iteratedScalarMatrixEquiv_involution]

/-- Actual rational scalar-extension similitudes in split matrix coordinates. -/
def scalarSimilitudesEquiv :
    (σ.rationalInvolution.baseChange S).similitudes ≃*
      (harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished).similitudes :=
  AlgebraInvolution.similitudesEquiv _ _ (C.scalarMatrixEquiv b S)
    (C.scalarMatrixEquiv_involution S b)

@[simp] theorem scalarSimilitudesEquiv_multiplier
    (g : (σ.rationalInvolution.baseChange S).similitudes) :
    (harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished).multiplier
      (C.scalarSimilitudesEquiv S b g) =
      (σ.rationalInvolution.baseChange S).multiplier g :=
  AlgebraInvolution.similitudesEquiv_multiplier _ _ _ _ g

/-- Actual rational scalar-extension unitary points in split matrix coordinates. -/
def scalarUnitaryEquiv :
    (σ.rationalInvolution.baseChange S).unitary ≃*
      (harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished).unitary :=
  AlgebraInvolution.unitaryEquiv _ _ (C.scalarMatrixEquiv b S)
    (C.scalarMatrixEquiv_involution S b)

theorem scalarUnitaryEquiv_inclusion (g : (σ.rationalInvolution.baseChange S).unitary) :
    (harrisScalarMatrixInvolution S n (E →+* ℝ) C.distinguished).unitaryInclusion
      (C.scalarUnitaryEquiv S b g) =
      C.scalarSimilitudesEquiv S b ((σ.rationalInvolution.baseChange S).unitaryInclusion g) :=
  AlgebraInvolution.unitaryEquiv_inclusion _ _ _ _ g

end HarrisSignatureCharts
end Langlands.Shimura

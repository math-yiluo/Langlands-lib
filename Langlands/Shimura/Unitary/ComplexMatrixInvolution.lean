import Langlands.Shimura.Unitary.ComplexMatrixSplitting

noncomputable section
open scoped TensorProduct Classical

namespace Langlands.Shimura.AlgebraInvolution

variable {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

/-- Transport an algebra involution along an actual algebra isomorphism. -/
def transport (σ : AlgebraInvolution R A) (e : A ≃ₐ[R] B) : AlgebraInvolution R B where
  linear := e.toLinearMap.comp (σ.linear.comp e.symm.toLinearMap)
  map_one := by change e (σ (e.symm 1)) = 1; simp
  map_mul x y := by change e (σ (e.symm (x * y))) = _; simp
  involutive x := by change e (σ (e.symm (e (σ (e.symm x))))) = x; simp

@[simp] theorem transport_apply (σ : AlgebraInvolution R A) (e : A ≃ₐ[R] B) (x : B) :
    transport σ e x = e (σ (e.symm x)) := rfl

@[simp] theorem transport_equiv (σ : AlgebraInvolution R A) (e : A ≃ₐ[R] B) (x : A) :
    transport σ e (e x) = e (σ x) := by simp

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.ComplexMatrix

/-- Linear signature transpose, with no conjugation on the complex scalars. -/
def signatureTranspose (n r : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := signatureMatrix n r * M.transpose * signatureMatrix n r

@[simp] theorem signatureTranspose_entry (n r : ℕ) (M : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    signatureTranspose n r M i j =
      (if i.val < r then 1 else -1) * M j i * (if j.val < r then 1 else -1) := by
  simp [signatureTranspose, signatureMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]

@[simp] theorem signatureAdjoint_entry (n r : ℕ) (M : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    signatureAdjoint n r M i j =
      (if i.val < r then 1 else -1) * star (M j i) * (if j.val < r then 1 else -1) := by
  change (signatureMatrix n r * M.conjTranspose * signatureMatrix n r) i j = _
  simp [signatureMatrix, Matrix.diagonal_mul, Matrix.mul_diagonal]

@[simp] theorem signatureTranspose_add (n r : ℕ) (M N : Matrix (Fin n) (Fin n) ℂ) :
    signatureTranspose n r (M + N) = signatureTranspose n r M + signatureTranspose n r N := by
  simp [signatureTranspose, Matrix.transpose_add, mul_add, add_mul]

@[simp] theorem signatureTranspose_smul (n r : ℕ) (z : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    signatureTranspose n r (z • M) = z • signatureTranspose n r M := by
  ext i j
  simp only [signatureTranspose_entry, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The real adjoint, after complexification, swaps the two signature-transpose factors. -/
theorem complexEquiv_adjoint (n r : ℕ) (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    complexEquiv n ((signatureAdjoint n r).baseChange ℂ x) =
      (signatureTranspose n r (complexEquiv n x).2,
       signatureTranspose n r (complexEquiv n x).1) := by
  induction x using TensorProduct.inductionOn with
  | tmul z M =>
    simp only [AlgebraInvolution.baseChange_tmul, complexEquiv_tmul,
      signatureTranspose_smul]
    apply Prod.ext
    · ext i j
      simp [Matrix.smul_apply, Matrix.map_apply]
    · ext i j
      simp only [Matrix.smul_apply, Matrix.map_apply, signatureAdjoint_entry,
        signatureTranspose_entry, star_mul, star_star]
      split_ifs <;> simp
  | add x y hx hy =>
    simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add,
      signatureTranspose_add, Prod.mk_add_mk]

/-- The complex-linear involution on the two split matrix factors. -/
def splitSignatureInvolution (n r : ℕ) :
    AlgebraInvolution ℂ (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
  ((signatureAdjoint n r).baseChange ℂ).transport (complexEquiv n)

@[simp] theorem splitSignatureInvolution_apply (n r : ℕ)
    (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    splitSignatureInvolution n r p =
      (signatureTranspose n r p.2, signatureTranspose n r p.1) := by
  rw [splitSignatureInvolution, AlgebraInvolution.transport_apply, complexEquiv_adjoint]
  simp

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura

/-- Complex matrix involution at every real place, with the Harris signatures. -/
def harrisComplexMatrixInvolution (n : ℕ) (I : Type*) [DecidableEq I]
    (distinguished : I) : AlgebraInvolution ℂ
      (I → Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) where
  linear :=
    { toFun := fun x τ => ComplexMatrix.splitSignatureInvolution n
        (if τ = distinguished then n - 1 else n) (x τ)
      map_add' := by intros; funext τ; exact AlgebraInvolution.apply_add _ _ _
      map_smul' := by intros; funext τ; exact AlgebraInvolution.apply_smul _ _ _ }
  map_one := by
    funext τ
    exact (ComplexMatrix.splitSignatureInvolution n
      (if τ = distinguished then n - 1 else n)).apply_one
  map_mul x y := by
    funext τ
    exact (ComplexMatrix.splitSignatureInvolution n
      (if τ = distinguished then n - 1 else n)).apply_mul (x τ) (y τ)
  involutive x := by
    funext τ
    exact (ComplexMatrix.splitSignatureInvolution n
      (if τ = distinguished then n - 1 else n)).apply_apply (x τ)

namespace HarrisSignatureCharts

universe u v w z
open NumberField Algebra Module
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

/-- The iterated complex matrix decomposition intertwines the actual involutions. -/
theorem iteratedComplexMatrixEquiv_involution (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)) :
    C.iteratedComplexMatrixEquiv b ((σ.rationalInvolution.baseChange ℝ).baseChange ℂ x) =
      harrisComplexMatrixInvolution n (E →+* ℝ) C.distinguished
        (C.iteratedComplexMatrixEquiv b x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    funext τ
    change C.iteratedComplexMatrixEquiv b
      ((σ.rationalInvolution.baseChange ℝ).baseChange ℂ (z ⊗ₜ[ℝ] x)) τ =
      ComplexMatrix.splitSignatureInvolution n (if τ = C.distinguished then n - 1 else n)
        (C.iteratedComplexMatrixEquiv b (z ⊗ₜ[ℝ] x) τ)
    simp only [AlgebraInvolution.baseChange_tmul, iteratedComplexMatrixEquiv_tmul,
      realMatrixEquiv_involution]
    change (z • signatureAdjoint n (if τ = C.distinguished then n - 1 else n)
        (C.realMatrixEquiv b x τ),
      z • (signatureAdjoint n (if τ = C.distinguished then n - 1 else n)
        (C.realMatrixEquiv b x τ)).map star) =
      ComplexMatrix.splitSignatureInvolution n (if τ = C.distinguished then n - 1 else n)
        (z • C.realMatrixEquiv b x τ, z • (C.realMatrixEquiv b x τ).map star)
    simpa only [ComplexMatrix.splitSignatureInvolution,
      AlgebraInvolution.baseChange_tmul, ComplexMatrix.complexEquiv_tmul] using
      (AlgebraInvolution.transport_equiv
        ((signatureAdjoint n (if τ = C.distinguished then n - 1 else n)).baseChange ℂ)
        (ComplexMatrix.complexEquiv n) (z ⊗ₜ[ℝ] C.realMatrixEquiv b x τ)).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Direct complex scalar extension has the same split involution. -/
theorem complexMatrixEquiv_involution (x : ℂ ⊗[ℚ] A) :
    C.complexMatrixEquiv b (σ.rationalInvolution.baseChange ℂ x) =
      harrisComplexMatrixInvolution n (E →+* ℝ) C.distinguished
        (C.complexMatrixEquiv b x) := by
  simp only [complexMatrixEquiv, AlgEquiv.trans_apply,
    AlgebraInvolution.baseChangeTowerEquiv_involution, iteratedComplexMatrixEquiv_involution]

/-- Complex similitudes of the actual algebra identified with the split matrix similitudes. -/
def complexSimilitudesEquiv :
    (σ.rationalInvolution.baseChange ℂ).similitudes ≃*
      (harrisComplexMatrixInvolution n (E →+* ℝ) C.distinguished).similitudes :=
  AlgebraInvolution.similitudesEquiv _ _ (C.complexMatrixEquiv b)
    (C.complexMatrixEquiv_involution b)

@[simp] theorem complexSimilitudesEquiv_multiplier
    (g : (σ.rationalInvolution.baseChange ℂ).similitudes) :
    (harrisComplexMatrixInvolution n (E →+* ℝ) C.distinguished).multiplier
      (C.complexSimilitudesEquiv b g) =
      (σ.rationalInvolution.baseChange ℂ).multiplier g :=
  AlgebraInvolution.similitudesEquiv_multiplier _ _ _ _ g

/-- Complex unitary points of the actual algebra identified with the split matrix unitary points. -/
def complexUnitaryEquiv :
    (σ.rationalInvolution.baseChange ℂ).unitary ≃*
      (harrisComplexMatrixInvolution n (E →+* ℝ) C.distinguished).unitary :=
  AlgebraInvolution.unitaryEquiv _ _ (C.complexMatrixEquiv b)
    (C.complexMatrixEquiv_involution b)

theorem complexUnitaryEquiv_inclusion (g : (σ.rationalInvolution.baseChange ℂ).unitary) :
    (harrisComplexMatrixInvolution n (E →+* ℝ) C.distinguished).unitaryInclusion
      (C.complexUnitaryEquiv b g) =
      C.complexSimilitudesEquiv b ((σ.rationalInvolution.baseChange ℂ).unitaryInclusion g) :=
  AlgebraInvolution.unitaryEquiv_inclusion _ _ _ _ g

end HarrisSignatureCharts
end Langlands.Shimura

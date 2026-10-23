import Langlands.Shimura.Unitary.ComplexMatrixSplitting

noncomputable section
open Algebra Module
open scoped TensorProduct Classical
attribute [local instance 1100] Algebra.toModule

namespace Langlands.Shimura.ComplexMatrix

variable (S : Type*) [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- Ordered matrix splitting over every commutative complex coefficient algebra. -/
def scalarEquiv (n : ℕ) :
    S ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ ≃ₐ[S]
      Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S :=
  (tensorAlgEquiv ℝ S ℂ n).trans
    ((DeligneTorus.tensorSplitEquiv S).mapMatrix.trans (prodAlgEquiv S S n S))

private theorem split_complexMap (w : ℂ) :
    DeligneTorus.splitEquiv S (DeligneTorus.complexMap S w) =
      (algebraMap ℂ S w, algebraMap ℂ S (star w)) := by
  rw [DeligneTorus.splitEquiv_apply]
  simp only [DeligneTorus.complexMap_re, DeligneTorus.complexMap_im]
  have hw : algebraMap ℂ S w =
      algebraMap ℝ S w.re + algebraMap ℝ S w.im * algebraMap ℂ S Complex.I := by
    have h := congrArg (algebraMap ℂ S) (Complex.re_add_im w)
    simpa only [map_add, map_mul, Complex.coe_algebraMap,
      IsScalarTower.algebraMap_apply ℝ ℂ S] using h.symm
  apply Prod.ext
  · exact hw.symm
  · have hw' : algebraMap ℂ S (star w) =
        algebraMap ℝ S w.re - algebraMap ℝ S w.im * algebraMap ℂ S Complex.I := by
      have h := congrArg (algebraMap ℂ S) (Complex.re_add_im (star w))
      simpa only [map_add, map_mul, Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_neg, map_neg, neg_mul, Complex.coe_algebraMap,
        IsScalarTower.algebraMap_apply ℝ ℂ S, sub_eq_add_neg] using h.symm
    exact hw'.symm

@[simp] theorem tensorSplitEquiv_scalar_tmul (s : S) (w : ℂ) :
    DeligneTorus.tensorSplitEquiv S (s ⊗ₜ[ℝ] w) =
      (s * algebraMap ℂ S w, s * algebraMap ℂ S (star w)) := by
  change DeligneTorus.splitEquiv S (DeligneTorus.fromTensor S (s ⊗ₜ[ℝ] w)) = _
  rw [DeligneTorus.fromTensor_tmul, map_smul, split_complexMap]
  rfl

@[simp] theorem scalarEquiv_tmul (n : ℕ) (s : S) (M : Matrix (Fin n) (Fin n) ℂ) :
    scalarEquiv S n (s ⊗ₜ[ℝ] M) =
      (s • M.map (algebraMap ℂ S), s • M.map (fun z => algebraMap ℂ S (star z))) := by
  apply Prod.ext
  · ext i j
    change (DeligneTorus.tensorSplitEquiv S (s ⊗ₜ[ℝ] M i j)).1 = _
    simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  · ext i j
    change (DeligneTorus.tensorSplitEquiv S (s ⊗ₜ[ℝ] M i j)).2 = _
    simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]

variable {T : Type*} [CommRing T] [Algebra ℂ T] [Algebra ℝ T]
  [IsScalarTower ℝ ℂ T]

/-- The matrix splitting commutes with change of complex coefficient algebra. -/
theorem scalarEquiv_natural (n : ℕ) (f : S →ₐ[ℂ] T)
    (x : S ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    scalarEquiv T n (AlgebraInvolution.changeCoefficients (f.restrictScalars ℝ) x) =
      ((scalarEquiv S n x).1.map f, (scalarEquiv S n x).2.map f) := by
  induction x using TensorProduct.inductionOn with
  | tmul s M =>
    apply Prod.ext <;> ext i j <;>
      simp [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    apply Prod.ext <;> ext i j <;> simp [Matrix.map_apply]

end Langlands.Shimura.ComplexMatrix

namespace Langlands.Shimura.HarrisSignatureCharts

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
  {ι : Type z} [Fintype ι] (b : Module.Basis ι E A)
  (S : Type*) [CommRing S] [Algebra ℂ S] [Algebra ℝ S] [IsScalarTower ℝ ℂ S]

/-- The real Harris matrix decomposition after extension to any complex coefficient algebra. -/
def iteratedScalarMatrixEquiv : S ⊗[ℝ] (ℝ ⊗[ℚ] A) ≃ₐ[S]
    ((E →+* ℝ) → Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (C.realMatrixEquiv b)).trans
    ((Algebra.TensorProduct.piRight ℝ S S
      (fun _ : E →+* ℝ => Matrix (Fin n) (Fin n) ℂ)).trans
      (AlgEquiv.piCongrRight (fun _ => ComplexMatrix.scalarEquiv S n)))

@[simp] theorem iteratedScalarMatrixEquiv_tmul (s : S) (x : ℝ ⊗[ℚ] A)
    (τ : E →+* ℝ) :
    C.iteratedScalarMatrixEquiv b S (s ⊗ₜ[ℝ] x) τ =
      (s • (C.realMatrixEquiv b x τ).map (algebraMap ℂ S),
       s • (C.realMatrixEquiv b x τ).map (fun z => algebraMap ℂ S (star z))) := by
  simp [iteratedScalarMatrixEquiv]

variable [Algebra ℚ S] [IsScalarTower ℚ ℝ S]

/-- Direct rational scalar extension has the same matrix decomposition over a complex algebra. -/
def scalarMatrixEquiv : S ⊗[ℚ] A ≃ₐ[S]
    ((E →+* ℝ) → Matrix (Fin n) (Fin n) S × Matrix (Fin n) (Fin n) S) :=
  (AlgebraInvolution.baseChangeTowerEquiv ℚ ℝ S A).trans
    (C.iteratedScalarMatrixEquiv b S)

@[simp] theorem scalarMatrixEquiv_tmul (s : S) (a : A) (τ : E →+* ℝ) :
    C.scalarMatrixEquiv b S (s ⊗ₜ[ℚ] a) τ =
      (s • (C.evaluation a τ).map (algebraMap ℂ S),
       s • (C.evaluation a τ).map (fun z => algebraMap ℂ S (star z))) := by
  simp only [scalarMatrixEquiv, AlgEquiv.trans_apply,
    AlgebraInvolution.baseChangeTowerEquiv_tmul, iteratedScalarMatrixEquiv_tmul,
    realMatrixEquiv_one_tmul]

end Langlands.Shimura.HarrisSignatureCharts

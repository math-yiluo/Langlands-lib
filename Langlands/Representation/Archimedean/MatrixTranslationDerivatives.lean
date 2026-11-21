import Langlands.Representation.Archimedean.MatrixTraceContraction
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Genuine derivatives of left and right matrix translations -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Matrix.Norms.Operator ContDiff

namespace Langlands.Archimedean

universe uF uV

variable {F : Type uF} [RCLike F] {n : ℕ}
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

local notation "M" => Matrix (Fin n) (Fin n) F

/-- Derivative along a left translation, with tangent argument `X * g`. -/
def matrixLeftDerivative (X : M) (f : M → V) (g : M) : V :=
  fderiv ℝ f g (X * g)

/-- Derivative along a right translation, with tangent argument `g * X`. -/
def matrixRightDerivative (X : M) (f : M → V) (g : M) : V :=
  fderiv ℝ f g (g * X)

theorem contDiff_matrixLeftDerivative {f : M → V} (hf : ContDiff ℝ ∞ f) (X : M) :
    ContDiff ℝ ∞ (matrixLeftDerivative X f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_const.mul contDiff_id)

theorem contDiff_matrixRightDerivative {f : M → V} (hf : ContDiff ℝ ∞ f) (X : M) :
    ContDiff ℝ ∞ (matrixRightDerivative X f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply (contDiff_id.mul contDiff_const)

theorem tsupport_matrixLeftDerivative_subset (X : M) (f : M → V) :
    tsupport (matrixLeftDerivative X f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro g hg
  apply support_fderiv_subset ℝ
  intro hz
  apply hg
  change fderiv ℝ f g (X * g) = 0
  rw [hz, zero_apply]

private theorem fderiv_field_eval {f : M → V} (hf : ContDiff ℝ ∞ f)
    (Q : M →L[ℝ] M) (g Z : M) :
    fderiv ℝ (fun a => fderiv ℝ f a (Q a)) g Z =
      fderiv ℝ f g (Q Z) + fderiv ℝ (fderiv ℝ f) g Z (Q g) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) g :=
    (hf.fderiv_right (m := ∞) (by simp)).contDiffAt.differentiableAt (by simp)
  rw [fderiv_clm_apply hdf Q.differentiableAt, Q.fderiv]
  rfl

theorem matrixLeftDerivative_iterate {f : M → V} (hf : ContDiff ℝ ∞ f) (X Y g : M) :
    matrixLeftDerivative X (matrixLeftDerivative Y f) g =
      fderiv ℝ f g (Y * (X * g)) + fderiv ℝ (fderiv ℝ f) g (X * g) (Y * g) :=
  fderiv_field_eval hf (ContinuousLinearMap.mul ℝ M Y) g (X * g)

theorem matrixRightDerivative_iterate {f : M → V} (hf : ContDiff ℝ ∞ f) (X Y g : M) :
    matrixRightDerivative X (matrixRightDerivative Y f) g =
      fderiv ℝ f g ((g * X) * Y) + fderiv ℝ (fderiv ℝ f) g (g * X) (g * Y) :=
  fderiv_field_eval hf ((ContinuousLinearMap.mul ℝ M).flip Y) g (g * X)

/-- Commuting two left-translation derivatives reverses the matrix
commutator because their fields are right invariant. -/
theorem matrixLeftDerivative_commutator {f : M → V} (hf : ContDiff ℝ ∞ f) (X Y : M) :
    matrixLeftDerivative X (matrixLeftDerivative Y f) -
      matrixLeftDerivative Y (matrixLeftDerivative X f) = matrixLeftDerivative (Y * X - X * Y) f := by
  funext g
  simp only [Pi.sub_apply, matrixLeftDerivative_iterate hf]
  rw [(hf.contDiffAt.isSymmSndFDerivAt (x := g) (by simp)) (X * g) (Y * g),
    add_sub_add_right_eq_sub]
  simp only [matrixLeftDerivative, sub_mul, mul_assoc, map_sub]

/-- The quadratic real trace Casimir, acting on smooth matrix functions. -/
def matrixTraceCasimir (f : M → V) (g : M) : V :=
  ∑ i, matrixLeftDerivative (matrixTraceUnit F n i)
    (matrixLeftDerivative (matrixTraceDualUnit F n i) f) g

/-- Matrix conjugation viewed as a real linear equivalence. -/
def matrixRealConjugation (g : Mˣ) : M ≃ₗ[ℝ] M :=
  { toFun := fun X => g.val * X * g⁻¹.val
    invFun := fun X => g⁻¹.val * X * g.val
    left_inv := fun X => by simp [mul_assoc]
    right_inv := fun X => by simp [mul_assoc]
    map_add' := fun X Y => by simp [mul_add, add_mul]
    map_smul' := fun r X => by simp }

@[simp]
theorem matrixRealConjugation_apply (g : Mˣ) (X : M) :
    matrixRealConjugation g X = g.val * X * g⁻¹.val := rfl

private def matrixRightHessian (f : M → V) (g : M) : M →ₗ[ℝ] M →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ
    (fun X Y => fderiv ℝ (fderiv ℝ f) g (g * X) (g * Y))
    (fun X₁ X₂ Y => by simp [mul_add, map_add])
    (fun r X Y => by simp [map_smul])
    (fun X Y₁ Y₂ => by simp [mul_add, map_add])
    (fun r X Y => by simp [map_smul])

private def matrixRightFirstOrder (f : M → V) (g : M) : M →ₗ[ℝ] M →ₗ[ℝ] V :=
  LinearMap.mk₂ ℝ
    (fun X Y => fderiv ℝ f g (g * (X * Y)))
    (fun X₁ X₂ Y => by simp [add_mul, mul_add, map_add])
    (fun r X Y => by simp [map_smul])
    (fun X Y₁ Y₂ => by simp [mul_add, map_add])
    (fun r X Y => by simp [map_smul])

/-- Iterating the right-translation fields gives the same trace
Casimir at every invertible matrix. -/
theorem matrixTraceCasimir_eq_right {f : M → V} (hf : ContDiff ℝ ∞ f) (g : Mˣ) :
    matrixTraceCasimir f g.val =
      ∑ i, matrixRightDerivative (matrixTraceUnit F n i)
        (matrixRightDerivative (matrixTraceDualUnit F n i) f) g.val := by
  let e : M ≃ₗ[ℝ] M := matrixRealConjugation g⁻¹
  have he (X Y : M) : matrixRealTracePairing F n (e X) (e Y) = matrixRealTracePairing F n X Y :=
    matrixRealTracePairing_units_conj F n g⁻¹ X Y
  have he₁ (X : M) : g.val * e X = X * g.val := by
    change g.val * (g⁻¹.val * X * g.val) = _
    simp [← mul_assoc]
  have he₂ (X Y : M) : g.val * (e Y * e X) = Y * (X * g.val) := by
    rw [← mul_assoc, he₁, mul_assoc, he₁]
  let B := matrixRightHessian f g.val
  let C := matrixRightFirstOrder f g.val
  have hleft (X Y : M) :
      matrixLeftDerivative X (matrixLeftDerivative Y f) g.val = C (e Y) (e X) + B (e X) (e Y) := by
    rw [matrixLeftDerivative_iterate hf]
    change _ = fderiv ℝ f g.val (g.val * (e Y * e X)) +
      fderiv ℝ (fderiv ℝ f) g.val (g.val * e X) (g.val * e Y)
    rw [he₂, he₁, he₁]
  have hright (X Y : M) :
      matrixRightDerivative X (matrixRightDerivative Y f) g.val = C X Y + B X Y := by
    rw [matrixRightDerivative_iterate hf, mul_assoc]
    rfl
  simp only [matrixTraceCasimir, hleft, hright, Finset.sum_add_distrib]
  rw [sum_matrixTraceContraction_invariant F n e he B]
  congr 1
  let C' := LinearMap.flip C
  exact (sum_matrixTraceContraction_invariant F n e he C').trans
    (sum_matrixTraceContraction_swap F n C)

/-- A smooth linear anti-automorphism exchanges left and right translation fields. -/
theorem matrixLeftDerivative_comp_anti (e : M ≃ₗ[ℝ] M)
    (he : ∀ X Y : M, e (X * Y) = e Y * e X) {f : M → V} (hf : ContDiff ℝ ∞ f) (X : M) :
    matrixLeftDerivative X (f ∘ e) = matrixRightDerivative (e X) f ∘ e := by
  funext g
  let L := e.toLinearMap.toContinuousLinearMap
  have hd : DifferentiableAt ℝ f (L g) := hf.contDiffAt.differentiableAt (by simp)
  have h := (hd.hasFDerivAt.comp g L.hasFDerivAt).fderiv
  change fderiv ℝ (f ∘ L) g (X * g) = fderiv ℝ f (L g) (L g * e X)
  rw [h, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ f (e g)) (he X g)

/-- A trace-preserving linear anti-automorphism commutes with the Casimir
on invertible matrices. -/
theorem matrixTraceCasimir_comp_anti (e : M ≃ₗ[ℝ] M)
    (he : ∀ X Y : M, e (X * Y) = e Y * e X) (he₁ : e 1 = 1)
    (ht : ∀ X Y, matrixRealTracePairing F n (e X) (e Y) = matrixRealTracePairing F n X Y)
    {f : M → V} (hf : ContDiff ℝ ∞ f) (g : Mˣ) :
    matrixTraceCasimir (f ∘ e) g.val = matrixTraceCasimir f (e g.val) := by
  let h : Mˣ :=
    { val := e g.val
      inv := e g⁻¹.val
      val_inv := by rw [← he, Units.inv_mul, he₁]
      inv_val := by rw [← he, Units.mul_inv, he₁] }
  have htrans (X Y : M) :
      matrixLeftDerivative X (matrixLeftDerivative Y (f ∘ e)) g.val =
        matrixRightDerivative (e X) (matrixRightDerivative (e Y) f) h.val := by
    rw [matrixLeftDerivative_comp_anti e he hf,
      matrixLeftDerivative_comp_anti e he (contDiff_matrixRightDerivative hf (e Y))]
    rfl
  let B := matrixRightFirstOrder f h.val + matrixRightHessian f h.val
  have hB (X Y : M) :
      matrixRightDerivative X (matrixRightDerivative Y f) h.val = B X Y := by
    rw [matrixRightDerivative_iterate hf, mul_assoc]
    rfl
  change matrixTraceCasimir (f ∘ e) g.val = matrixTraceCasimir f h.val
  rw [matrixTraceCasimir_eq_right hf h]
  simp only [matrixTraceCasimir, htrans, hB]
  exact sum_matrixTraceContraction_invariant F n e ht B

/-- In particular, transpose followed by any fixed matrix conjugation
commutes with the trace Casimir. -/
theorem matrixTraceCasimir_comp_transposeConjugation {f : M → V}
    (hf : ContDiff ℝ ∞ f) (w g : Mˣ) :
    matrixTraceCasimir (fun X => f (w.val * X.transpose * w⁻¹.val)) g.val =
      matrixTraceCasimir f (w.val * g.val.transpose * w⁻¹.val) := by
  let e : M ≃ₗ[ℝ] M := (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ F).trans
    (matrixRealConjugation w)
  have he (X Y : M) : e (X * Y) = e Y * e X := by
    change w.val * (X * Y).transpose * w⁻¹.val =
      (w.val * Y.transpose * w⁻¹.val) * (w.val * X.transpose * w⁻¹.val)
    simp [Matrix.transpose_mul, mul_assoc]
  have he₁ : e 1 = 1 := by
    change w.val * (1 : M).transpose * w⁻¹.val = 1
    simp
  have ht (X Y : M) : matrixRealTracePairing F n (e X) (e Y) = matrixRealTracePairing F n X Y :=
    (matrixRealTracePairing_units_conj F n w X.transpose Y.transpose).trans
      (matrixRealTracePairing_transpose F n X Y)
  exact matrixTraceCasimir_comp_anti e he he₁ ht hf g

end Langlands.Archimedean

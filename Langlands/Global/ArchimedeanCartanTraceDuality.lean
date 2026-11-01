import Langlands.Global.ArchimedeanCartanTraceForm
import Langlands.Global.ArchimedeanCartanSymmetricAlgebra
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Trace duality of the actual complex Cartan spaces -/

noncomputable section
universe u v
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

private theorem complexBaseChange_symm {V : Type v}
    [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V) (hS : B.IsSymm) :
    (B.baseChange ℂ).IsSymm :=
  LinearMap.BilinForm.isSymm_iff.mpr
    (LinearMap.BilinForm.IsSymm.baseChange ℂ (LinearMap.BilinForm.isSymm_iff.mp hS))

private theorem complexBaseChange_nondegenerate {V : Type v}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hS : B.IsSymm) :
    (B.baseChange ℂ).Nondegenerate := by
  classical
  let b := Module.finBasis ℝ V
  let d := B.dualBasis hB b
  have hcoord (x : ℂ ⊗[ℝ] V) (i : Fin (Module.finrank ℝ V)) :
      B.baseChange ℂ x (1 ⊗ₜ[ℝ] b i) = (d.baseChange ℂ).repr x i := by
    induction x using TensorProduct.inductionOn with
    | tmul z x => simp [d]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, Finsupp.add_apply]
  have hleft : (B.baseChange ℂ).SeparatingLeft := by
    intro x hx
    apply (d.baseChange ℂ).repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using
      (hcoord x i).symm.trans (hx (1 ⊗ₜ[ℝ] b i))
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  rw [(complexBaseChange_symm B hS).eq]
  exact hx y

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance cartanTraceDuality_realLieAlgebra_finiteDimensional :
    FiniteDimensional ℝ (RealLieAlgebra K n) :=
  FiniteDimensional.of_injective (realLieAlgebraToMatrix K n).toLinearMap
    (realLieAlgebraToMatrix K n).injective

/-- Restrict the actual real matrix trace form to the self-adjoint complement. -/
def cartanTraceForm : LinearMap.BilinForm ℝ (cartanComplement K n) :=
  (matrixTraceForm K n).restrict (cartanComplement K n)

@[simp]
theorem cartanTraceForm_apply (X Y : cartanComplement K n) :
    cartanTraceForm K n X Y = matrixTraceForm K n X Y := rfl

theorem cartanTraceForm_symm : (cartanTraceForm K n).IsSymm :=
  ⟨fun X Y => matrixTraceForm_symm K n X Y⟩

theorem cartanTraceForm_nondegenerate : (cartanTraceForm K n).Nondegenerate := by
  have hself (X : cartanComplement K n) (h : cartanTraceForm K n X X = 0) : X = 0 := by
    apply Subtype.ext
    apply (cartanPositiveForm_self_eq_zero_iff K n X).mp
    rw [← matrixTraceForm_complement_right K n X X X.property]
    exact h
  exact ⟨fun X h => hself X (h X), fun X h => hself X (h X)⟩

/-- Extend the actual real trace form to the full complex Lie vector space. -/
def complexMatrixTraceForm : LinearMap.BilinForm ℂ (ComplexLieAlgebra K n) :=
  (matrixTraceForm K n).baseChange ℂ

/-- Extend the restricted actual trace form to the complex Cartan complement. -/
def complexCartanTraceForm : LinearMap.BilinForm ℂ (ComplexCartanComplement K n) :=
  (cartanTraceForm K n).baseChange ℂ

@[simp]
theorem complexMatrixTraceForm_tmul (z w : ℂ) (X Y : RealLieAlgebra K n) :
    complexMatrixTraceForm K n (z ⊗ₜ[ℝ] X) (w ⊗ₜ[ℝ] Y) =
      matrixTraceForm K n X Y • (z * w) := rfl

@[simp]
theorem complexCartanTraceForm_tmul (z w : ℂ) (X Y : cartanComplement K n) :
    complexCartanTraceForm K n (z ⊗ₜ[ℝ] X) (w ⊗ₜ[ℝ] Y) =
      cartanTraceForm K n X Y • (z * w) := rfl

theorem complexMatrixTraceForm_symm : (complexMatrixTraceForm K n).IsSymm :=
  complexBaseChange_symm _ ⟨matrixTraceForm_symm K n⟩

theorem complexCartanTraceForm_symm : (complexCartanTraceForm K n).IsSymm :=
  complexBaseChange_symm _ (cartanTraceForm_symm K n)

theorem complexMatrixTraceForm_nondegenerate :
    (complexMatrixTraceForm K n).Nondegenerate :=
  complexBaseChange_nondegenerate _ (matrixTraceForm_nondegenerate K n)
    ⟨matrixTraceForm_symm K n⟩

theorem complexCartanTraceForm_nondegenerate :
    (complexCartanTraceForm K n).Nondegenerate :=
  complexBaseChange_nondegenerate _ (cartanTraceForm_nondegenerate K n)
    (cartanTraceForm_symm K n)

/-- The full complex trace identification with the algebraic dual. -/
def complexTraceDualEquiv :
    ComplexLieAlgebra K n ≃ₗ[ℂ] Module.Dual ℂ (ComplexLieAlgebra K n) :=
  (complexMatrixTraceForm K n).toDual (complexMatrixTraceForm_nondegenerate K n)

/-- The complementary complex trace identification with the algebraic dual. -/
def cartanTraceDualEquiv :
    ComplexCartanComplement K n ≃ₗ[ℂ] Module.Dual ℂ (ComplexCartanComplement K n) :=
  (complexCartanTraceForm K n).toDual (complexCartanTraceForm_nondegenerate K n)

@[simp]
theorem complexTraceDualEquiv_apply (X Y : ComplexLieAlgebra K n) :
    complexTraceDualEquiv K n X Y = complexMatrixTraceForm K n X Y := rfl

@[simp]
theorem cartanTraceDualEquiv_apply (X Y : ComplexCartanComplement K n) :
    cartanTraceDualEquiv K n X Y = complexCartanTraceForm K n X Y := rfl

theorem matrixTraceForm_conjugation (g : InfiniteAdelicGL K n)
    (X Y : RealLieAlgebra K n) :
    matrixTraceForm K n (realLieConjugation K n g X) (realLieConjugation K n g Y) =
      matrixTraceForm K n X Y := by
  simp only [matrixTraceForm_apply, realLieAlgebraToMatrix_realLieConjugation, map_inv]
  have hproduct :
      ((archimedeanGLCoordinates K n g).val * realLieAlgebraToMatrix K n X *
          (archimedeanGLCoordinates K n g)⁻¹.val) *
        ((archimedeanGLCoordinates K n g).val * realLieAlgebraToMatrix K n Y *
          (archimedeanGLCoordinates K n g)⁻¹.val) =
      (archimedeanGLCoordinates K n g).val *
        (realLieAlgebraToMatrix K n X * realLieAlgebraToMatrix K n Y) *
          (archimedeanGLCoordinates K n g)⁻¹.val := by
    simp [mul_assoc]
  rw [hproduct, Matrix.trace_units_conj]

theorem complexMatrixTraceForm_conjugation (g : InfiniteAdelicGL K n)
    (X Y : ComplexLieAlgebra K n) :
    complexMatrixTraceForm K n (complexLieConjugation K n g X)
        (complexLieConjugation K n g Y) = complexMatrixTraceForm K n X Y := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    induction Y using TensorProduct.inductionOn with
    | tmul w Y => simp only [complexLieConjugation_tmul, complexMatrixTraceForm_tmul,
        matrixTraceForm_conjugation]
    | add Y Z hY hZ => simp only [map_add, hY, hZ]
  | add X Z hX hZ => simp only [map_add, LinearMap.add_apply, hX, hZ]

theorem matrixTraceForm_cartanProjection (X : RealLieAlgebra K n)
    (Y : cartanComplement K n) :
    matrixTraceForm K n X Y =
      cartanTraceForm K n (cartanComplementProjection K n X) Y := by
  have hzero : matrixTraceForm K n (compactProjection K n X) Y = 0 := by
    rw [matrixTraceForm_complement_right K n _ _ Y.property]
    exact cartanPositiveForm_compact_complement K n _ _
      (compactProjection K n X).property Y.property
  calc
    matrixTraceForm K n X Y =
        matrixTraceForm K n
          ((compactProjection K n X : RealLieAlgebra K n) +
            cartanComplementProjection K n X) Y :=
      congrArg (fun Z => matrixTraceForm K n Z Y)
        (compactProjection_add_cartanComplementProjection K n X).symm
    _ = cartanTraceForm K n (cartanComplementProjection K n X) Y := by
      rw [LinearMap.BilinForm.add_left, hzero, zero_add]
      rfl

theorem complexMatrixTraceForm_cartanProjection (X : ComplexLieAlgebra K n)
    (Y : ComplexCartanComplement K n) :
    complexMatrixTraceForm K n X (cartanComplexInclusion K n Y) =
      complexCartanTraceForm K n (cartanComplexProjection K n X) Y := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    induction Y using TensorProduct.inductionOn with
    | tmul w Y => simp only [cartanComplexInclusion_tmul, cartanComplexProjection_tmul,
        complexMatrixTraceForm_tmul, complexCartanTraceForm_tmul,
        matrixTraceForm_cartanProjection]
    | add Y Z hY hZ => simp only [map_add, hY, hZ]
  | add X Z hX hZ => simp only [map_add, LinearMap.add_apply, hX, hZ]

theorem complexMatrixTraceForm_cartanInclusion (X Y : ComplexCartanComplement K n) :
    complexMatrixTraceForm K n (cartanComplexInclusion K n X)
        (cartanComplexInclusion K n Y) = complexCartanTraceForm K n X Y := by
  rw [complexMatrixTraceForm_cartanProjection, cartanComplexProjection_inclusion]

theorem complexCartanTraceForm_conjugation (k : standardInfiniteCompact K n)
    (X Y : ComplexCartanComplement K n) :
    complexCartanTraceForm K n (cartanComplexConjugation K n k X)
        (cartanComplexConjugation K n k Y) = complexCartanTraceForm K n X Y := by
  rw [← complexMatrixTraceForm_cartanInclusion,
    cartanComplexInclusion_conjugation, cartanComplexInclusion_conjugation,
    complexMatrixTraceForm_conjugation, complexMatrixTraceForm_cartanInclusion]

/-- Trace duality intertwines adjoint conjugation with the contragredient action. -/
theorem complexTraceDualEquiv_conjugation (g : InfiniteAdelicGL K n)
    (X : ComplexLieAlgebra K n) :
    complexTraceDualEquiv K n (complexLieConjugation K n g X) =
      (complexTraceDualEquiv K n X).comp (complexLieConjugation K n g⁻¹).toLinearMap := by
  apply LinearMap.ext
  intro Y
  change complexMatrixTraceForm K n (complexLieConjugation K n g X) Y =
    complexMatrixTraceForm K n X (complexLieConjugation K n g⁻¹ Y)
  simpa using complexMatrixTraceForm_conjugation K n g X
    (complexLieConjugation K n g⁻¹ Y)

/-- Complementary trace duality intertwines the entire compact group action. -/
theorem cartanTraceDualEquiv_conjugation (k : standardInfiniteCompact K n)
    (X : ComplexCartanComplement K n) :
    cartanTraceDualEquiv K n (cartanComplexConjugation K n k X) =
      (cartanTraceDualEquiv K n X).comp (cartanComplexConjugation K n k⁻¹).toLinearMap := by
  apply LinearMap.ext
  intro Y
  change complexCartanTraceForm K n (cartanComplexConjugation K n k X) Y =
    complexCartanTraceForm K n X (cartanComplexConjugation K n k⁻¹ Y)
  simpa using complexCartanTraceForm_conjugation K n k X
    (cartanComplexConjugation K n k⁻¹ Y)

/-- Under trace duality, Cartan projection is restriction of dual functionals. -/
theorem cartanTraceDualEquiv_projection (X : ComplexLieAlgebra K n) :
    cartanTraceDualEquiv K n (cartanComplexProjection K n X) =
      (complexTraceDualEquiv K n X).comp (cartanComplexInclusion K n) := by
  apply LinearMap.ext
  intro Y
  exact (complexMatrixTraceForm_cartanProjection K n X Y).symm

end Langlands.Global.ArchimedeanGL

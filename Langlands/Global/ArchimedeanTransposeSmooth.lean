import Langlands.Global.ArchimedeanTransposeInverse
import Langlands.Global.ArchimedeanCenterFinite
import Langlands.Group.GL.Maps

/-! # Transpose-inverse pullback on actual archimedean smooth functions -/

noncomputable section
universe u
open scoped Classical TensorProduct Matrix.Norms.Operator Manifold ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

open NumberField Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-- Transpose as a continuous real-linear matrix equivalence. -/
def matrixTransposeLinear : ArchimedeanMatrix F n ≃L[ℝ] ArchimedeanMatrix F n :=
  (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ
    (mixedEmbedding.mixedSpace F)).toContinuousLinearEquiv

@[simp]
theorem matrixTransposeLinear_apply (a : ArchimedeanMatrix F n) :
    matrixTransposeLinear F n a = a.transpose := rfl

/-- Transpose inverse is smooth in the actual units manifold. -/
theorem contMDiff_inverseTranspose :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ArchimedeanMatrix F n) ∞
      (inverseTranspose n (mixedEmbedding.mixedSpace F)) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ArchimedeanMatrix F n) ∞
    (fun g : ArchimedeanGL F n => matrixTransposeLinear F n (g⁻¹).val)
  exact (matrixTransposeLinear F n).contDiff.contMDiff.comp
    (Units.contMDiff_val.comp (contMDiff_inv 𝓘(ℝ, ArchimedeanMatrix F n) ∞))

omit [NumberField F] in
@[simp]
theorem coordinates_inverseTranspose
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)) :
    archimedeanGLCoordinates F n (inverseTranspose n (InfiniteAdeleRing F) g) =
      inverseTranspose n (mixedEmbedding.mixedSpace F) (archimedeanGLCoordinates F n g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change InfiniteAdeleRing.ringEquiv_mixedSpace F (g⁻¹ j i) =
    ((archimedeanGLCoordinates F n g)⁻¹) j i
  rw [← map_inv]
  rfl

omit [NumberField F] in
@[simp]
theorem coordinates_symm_inverseTranspose (g : ArchimedeanGL F n) :
    (archimedeanGLCoordinates F n).symm (inverseTranspose n (mixedEmbedding.mixedSpace F) g) =
      inverseTranspose n (InfiniteAdeleRing F) ((archimedeanGLCoordinates F n).symm g) := by
  apply (archimedeanGLCoordinates F n).injective
  simp

/-- Complex-linear pullback along transpose inverse on actual smooth functions. -/
def smoothTranspose : SmoothFunctions F n ≃ₗ[ℂ] SmoothFunctions F n where
  toFun f := ⟨fun g => f.val (inverseTranspose n (InfiniteAdeleRing F) g), by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞ _
    simpa only [Function.comp_def, coordinates_symm_inverseTranspose] using
      f.property.comp (contMDiff_inverseTranspose F n)⟩
  invFun f := ⟨fun g => f.val (inverseTranspose n (InfiniteAdeleRing F) g), by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞ _
    simpa only [Function.comp_def, coordinates_symm_inverseTranspose] using
      f.property.comp (contMDiff_inverseTranspose F n)⟩
  left_inv f := by ext g; simp
  right_inv f := by ext g; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem smoothTranspose_apply (f : SmoothFunctions F n)
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)) :
    (smoothTranspose F n f).val g = f.val (inverseTranspose n (InfiniteAdeleRing F) g) := rfl

@[simp]
theorem smoothTranspose_involutive (f : SmoothFunctions F n) :
    smoothTranspose F n (smoothTranspose F n f) = f := by ext g; simp

/-- An ambient matrix extension of transpose inverse, used only near units. -/
def matrixInverseTranspose (a : ArchimedeanMatrix F n) : ArchimedeanMatrix F n :=
  matrixTransposeLinear F n (Ring.inverse a)

@[simp]
theorem matrixInverseTranspose_unit (g : ArchimedeanGL F n) :
    matrixInverseTranspose F n g =
      (inverseTranspose n (mixedEmbedding.mixedSpace F) g).val := by
  simp only [matrixInverseTranspose, Ring.inverse_unit, matrixTransposeLinear_apply,
    inverseTranspose_coe]

/-- The ambient extension has the usual inversion derivative followed by transpose. -/
theorem hasFDerivAt_matrixInverseTranspose (g : ArchimedeanGL F n) :
    HasFDerivAt (matrixInverseTranspose F n)
      ((matrixTransposeLinear F n).toContinuousLinearMap.comp
        (-ContinuousLinearMap.mulLeftRight ℝ (ArchimedeanMatrix F n) (g⁻¹).val (g⁻¹).val))
      (g : ArchimedeanMatrix F n) :=
  (matrixTransposeLinear F n).toContinuousLinearMap.hasFDerivAt.comp _
    (hasFDerivAt_ringInverse (𝕜 := ℝ) g)

/-- The differential carries `gX` to `theta(g) (-Xᵗ)`. -/
theorem fderiv_matrixInverseTranspose_direction (g : ArchimedeanGL F n)
    (X : RealLieAlgebra F n) :
    fderiv ℝ (matrixInverseTranspose F n) (g : ArchimedeanMatrix F n)
      ((g : ArchimedeanMatrix F n) * realLieAlgebraToMatrix F n X) =
      (inverseTranspose n (mixedEmbedding.mixedSpace F) g).val *
        realLieAlgebraToMatrix F n (realLieIota F n X) := by
  rw [(hasFDerivAt_matrixInverseTranspose F n g).fderiv]
  change (-((g⁻¹).val * (g.val * realLieAlgebraToMatrix F n X) * (g⁻¹).val)).transpose =
    (g⁻¹).val.transpose * -(realLieAlgebraToMatrix F n X).transpose
  rw [← mul_assoc, Units.inv_mul, one_mul, Matrix.transpose_neg, Matrix.transpose_mul, mul_neg]

private theorem coordinateExtension_transpose (f : SmoothFunctions F n)
    (h : ArchimedeanGL F n) :
    coordinateExtension F n f (matrixInverseTranspose F n h) =
      (smoothTranspose F n f).val ((archimedeanGLCoordinates F n).symm h) := by
  rw [matrixInverseTranspose_unit, coordinateExtension_apply, smoothTranspose_apply,
    coordinates_symm_inverseTranspose]

/-- Pullback by transpose inverse intertwines the genuine real matrix derivatives. -/
theorem smoothTranspose_smoothDifferential (X : RealLieAlgebra F n)
    (f : SmoothFunctions F n) :
    smoothTranspose F n (smoothDifferential F n (realLieIota F n X) f) =
      smoothDifferential F n X (smoothTranspose F n f) := by
  apply Subtype.ext
  funext g
  rw [smoothTranspose_apply, smoothDifferential_eq_of_extension F n X (smoothTranspose F n f)
    (fun a => coordinateExtension F n f (matrixInverseTranspose F n a))
    (coordinateExtension_transpose F n f)]
  have hdiff : DifferentiableAt ℝ (coordinateExtension F n f)
      (matrixInverseTranspose F n (archimedeanGLCoordinates F n g)) := by
    rw [matrixInverseTranspose_unit]
    exact (coordinateExtension_contDiffAt F n f _).differentiableAt (by simp)
  rw [fderiv_fun_comp _ hdiff
    (hasFDerivAt_matrixInverseTranspose F n (archimedeanGLCoordinates F n g)).differentiableAt]
  change _ = fderiv ℝ (coordinateExtension F n f)
    (matrixInverseTranspose F n (archimedeanGLCoordinates F n g))
    ((fderiv ℝ (matrixInverseTranspose F n) (archimedeanGLCoordinates F n g))
      ((archimedeanGLCoordinates F n g : ArchimedeanMatrix F n) * realLieAlgebraToMatrix F n X))
  rw [fderiv_matrixInverseTranspose_direction, matrixInverseTranspose_unit,
    smoothDifferential_apply, coordinates_inverseTranspose]

/-- Right translations are twisted by the same transpose-inverse group automorphism. -/
theorem smoothTranspose_smoothRightAction
    (h : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing F)) (f : SmoothFunctions F n) :
    smoothTranspose F n (smoothRightAction F n (inverseTranspose n (InfiniteAdeleRing F) h) f) =
      smoothRightAction F n h (smoothTranspose F n f) := by
  ext g
  simp only [smoothTranspose_apply, smoothRightAction_apply, map_mul]

/-- Complex scalar extension of real differential covariance. -/
theorem smoothTranspose_complexSmoothLieAction (X : ComplexLieAlgebra F n)
    (f : SmoothFunctions F n) :
    smoothTranspose F n (complexSmoothLieAction F n (complexLieIota F n X) f) =
      complexSmoothLieAction F n X (smoothTranspose F n f) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexLieIota_tmul, complexSmoothLieAction_tmul,
      LinearMap.smul_apply, map_smul]
    rw [smoothTranspose_smoothDifferential]
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply, hX, hY]

/-- Pullback intertwines the genuine universal enveloping algebra actions. -/
theorem smoothTranspose_envelopingAction (a : EnvelopingAlgebra F n)
    (f : SmoothFunctions F n) :
    smoothTranspose F n (envelopingAction F n (envelopingIota F n a) f) =
      envelopingAction F n a (smoothTranspose F n f) := by
  revert f
  refine Quotient.inductionOn a ?_
  intro t
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ComplexLieAlgebra F n)
  change ∀ f : SmoothFunctions F n,
    smoothTranspose F n (envelopingAction F n (envelopingIota F n (q t)) f) =
      envelopingAction F n (q t) (smoothTranspose F n f)
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    intro f
    simp [Algebra.algebraMap_eq_smul_one]
  | ι X =>
    intro f
    change smoothTranspose F n
        (envelopingAction F n (envelopingIota F n (envelopingGenerator F n X)) f) =
      envelopingAction F n (envelopingGenerator F n X) (smoothTranspose F n f)
    simpa only [envelopingAction_generator, envelopingIota_generator] using
      smoothTranspose_complexSmoothLieAction F n X f
  | mul a b ha hb =>
    intro f
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, hb]
  | add a b ha hb =>
    intro f
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Restriction of covariance to the actual enveloping center. -/
theorem smoothTranspose_centerAction (z : EnvelopingCenter F n)
    (f : SmoothFunctions F n) :
    smoothTranspose F n (centerAction F n (centerIota F n z) f) =
      centerAction F n z (smoothTranspose F n f) := by
  simpa only [centerAction_apply, centerInclusion_centerIota] using
    smoothTranspose_envelopingAction F n (centerInclusion F n z) f

/-- The actual center orbit is transported by the pullback equivalence. -/
theorem centerOrbitSpan_smoothTranspose (f : SmoothFunctions F n) :
    centerOrbitSpan F n (smoothTranspose F n f) =
      (centerOrbitSpan F n f).map (smoothTranspose F n).toLinearMap := by
  rw [centerOrbitSpan_eq_range, centerOrbitSpan_eq_range]
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨centerAction F n (centerIota F n z) f,
      ⟨centerIota F n z, rfl⟩, smoothTranspose_centerAction F n z f⟩
  · rintro _ ⟨h, ⟨z, rfl⟩, rfl⟩
    obtain ⟨w, rfl⟩ := (centerIota F n).surjective z
    exact ⟨w, (smoothTranspose_centerAction F n w f).symm⟩

/-- Pullback restricts to a linear equivalence on actual center orbit spans. -/
def transposeCenterOrbitEquiv (f : SmoothFunctions F n) :
    centerOrbitSpan F n f ≃ₗ[ℂ] centerOrbitSpan F n (smoothTranspose F n f) :=
  (smoothTranspose F n).ofSubmodules _ _ (centerOrbitSpan_smoothTranspose F n f).symm

/-- Center finiteness is preserved and reflected by transpose inverse. -/
theorem isCenterFinite_smoothTranspose_iff (f : SmoothFunctions F n) :
    IsCenterFinite F n (smoothTranspose F n f) ↔ IsCenterFinite F n f :=
  (LinearMap.finite_iff_of_bijective
    (transposeCenterOrbitEquiv F n f).toLinearMap
    (transposeCenterOrbitEquiv F n f).bijective).symm

end Langlands.Global.ArchimedeanGL

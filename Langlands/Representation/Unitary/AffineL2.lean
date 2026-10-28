import Langlands.Analysis.NormalizedL2Pullback
import Langlands.Analysis.AffineChangeOfVariables
import Langlands.Group.GL.MirabolicAffine
import Mathlib.RepresentationTheory.Basic

/-! # Normalized affine action on actual complex L² -/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.AffineL2

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

/-- The actual inverse affine pullback, with the positive inverse half determinant. -/
def operator {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      GeneralLinear n F.Carrier → (Fin n → F.Carrier) →
        Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro _ _ μ _ A v
  exact NormalizedL2Pullback.isometryEquiv
    (AffineChangeOfVariables.measurableEquiv A v).symm
    (T.determinantNorm n A : ℝ≥0) (T.determinantNorm n A).ne_zero
    (AffineChangeOfVariables.padic_map_haar_symm F T n μ A v)

/-- The formula is an equality of representatives almost everywhere. -/
theorem coeFn_operator {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier) (f : Lp ℂ 2 μ),
        operator F T μ A v f =ᵐ[μ] fun x =>
          NormalizedL2Pullback.normalization (T.determinantNorm n A : ℝ≥0) •
            f ((A⁻¹).val.mulVec (x - v)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A v f
  exact NormalizedL2Pullback.coeFn_isometryEquiv _ _ _ _ f

@[simp] theorem norm_operator {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier) (f : Lp ℂ 2 μ),
        ‖operator F T μ A v f‖ = ‖f‖ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A v f
  exact (operator F T μ A v).norm_map f

@[simp] theorem operator_one_zero {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      operator F T μ (1 : GeneralLinear n F.Carrier) 0 =
        LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _
  unfold operator
  simp only [map_one, Units.val_one, AffineChangeOfVariables.measurableEquiv_one_zero,
    MeasurableEquiv.symm_refl]
  exact NormalizedL2Pullback.isometryEquiv_refl

/-- Left affine multiplication, at the level of actual L² vectors. -/
theorem operator_mul_apply {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A B : GeneralLinear n F.Carrier) (v w : Fin n → F.Carrier) (f : Lp ℂ 2 μ),
        operator F T μ A v (operator F T μ B w f) =
          operator F T μ (A * B) (v + A.val.mulVec w) f := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A B v w f
  have h := NormalizedL2Pullback.normalized_comp
    (AffineChangeOfVariables.measurableEquiv A v).symm
    (AffineChangeOfVariables.measurableEquiv B w).symm
    (T.determinantNorm n A : ℝ≥0) (T.determinantNorm n B : ℝ≥0)
    (T.determinantNorm n A).ne_zero (T.determinantNorm n B).ne_zero
    (AffineChangeOfVariables.padic_map_haar_symm F T n μ A v)
    (AffineChangeOfVariables.padic_map_haar_symm F T n μ B w) f
  have he : (AffineChangeOfVariables.measurableEquiv A v).symm.trans
      (AffineChangeOfVariables.measurableEquiv B w).symm =
      (AffineChangeOfVariables.measurableEquiv (A * B) (v + A.val.mulVec w)).symm := by
    rw [← MeasurableEquiv.trans_symm, AffineChangeOfVariables.measurableEquiv_trans]
  simpa only [operator, NormalizedL2Pullback.isometryEquiv_apply, he,
    map_mul, Units.val_mul] using h

/-- The equivalence-level multiplication law uses trans in application order. -/
theorem operator_mul {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A B : GeneralLinear n F.Carrier) (v w : Fin n → F.Carrier),
        (operator F T μ B w).trans (operator F T μ A v) =
          operator F T μ (A * B) (v + A.val.mulVec w) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A B v w
  apply LinearIsometryEquiv.ext
  intro f
  exact operator_mul_apply F T μ A B v w f

/-- The inverse is the operator at the actual inverse affine coordinates. -/
theorem operator_symm {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier),
        (operator F T μ A v).symm =
          operator F T μ A⁻¹ (-((A⁻¹).val.mulVec v)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A v
  have he : (AffineChangeOfVariables.measurableEquiv A⁻¹
      (-((A⁻¹).val.mulVec v))).symm = AffineChangeOfVariables.measurableEquiv A v := by
    rw [← AffineChangeOfVariables.measurableEquiv_symm, MeasurableEquiv.symm_symm]
  simp only [operator, NormalizedL2Pullback.isometryEquiv_symm,
    MeasurableEquiv.symm_symm, he, map_inv, Units.val_inv_eq_inv_val]

/-- The inverse-coordinate operator cancels the original operator on the left. -/
theorem operator_inv_apply {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier) (f : Lp ℂ 2 μ),
        operator F T μ A⁻¹ (-((A⁻¹).val.mulVec v)) (operator F T μ A v f) = f := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A v f
  rw [← operator_symm F T μ A v]
  exact (operator F T μ A v).symm_apply_apply f

/-- The inverse-coordinate operator also cancels on the right. -/
theorem operator_apply_inv {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier) (f : Lp ℂ 2 μ),
        operator F T μ A v (operator F T μ A⁻¹ (-((A⁻¹).val.mulVec v)) f) = f := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A v f
  rw [← operator_symm F T μ A v]
  exact (operator F T μ A v).apply_symm_apply f

open GeneralLinear.Mirabolic

/-- The isometry attached to an actual mirabolic matrix. -/
def mirabolicOperator {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      GeneralLinear.mirabolic n F.Carrier → (Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro _ _ μ _ g
  exact operator F T μ (linearPart g) (columnPart g)

/-- Identity of the actual mirabolic action. -/
@[simp] theorem mirabolicOperator_one {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      mirabolicOperator F T μ (1 : GeneralLinear.mirabolic n F.Carrier) =
        LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _
  have hc : columnPart (1 : GeneralLinear.mirabolic n F.Carrier) = 0 := by
    funext i
    simp [columnPart]
  simp only [mirabolicOperator, map_one, hc, operator_one_zero]

/-- The inherited mirabolic matrix multiplication gives the left action law. -/
theorem mirabolicOperator_mul {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (g h : GeneralLinear.mirabolic n F.Carrier),
        (mirabolicOperator F T μ h).trans (mirabolicOperator F T μ g) =
          mirabolicOperator F T μ (g * h) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ g h
  simpa only [mirabolicOperator, map_mul, columnPart_mul] using
    operator_mul F T μ (linearPart g) (linearPart h) (columnPart g) (columnPart h)

/-- Action on the literal matrix with leading block A and final column v. -/
@[simp] theorem mirabolicOperator_affineMatrix {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier),
        mirabolicOperator F T μ (affineMatrix A v) = operator F T μ A v := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A v
  simp only [mirabolicOperator, linearPart_affineMatrix, columnPart_affineMatrix]

/-- Almost-everywhere representative through the actual leading block and final column. -/
theorem coeFn_mirabolicOperator {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (g : GeneralLinear.mirabolic n F.Carrier) (f : Lp ℂ 2 μ),
        mirabolicOperator F T μ g f =ᵐ[μ] fun x =>
          NormalizedL2Pullback.normalization (T.determinantNorm n (linearPart g) : ℝ≥0) •
            f (((linearPart g)⁻¹).val.mulVec (x - columnPart g)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ g f
  exact coeFn_operator F T μ (linearPart g) (columnPart g) f

/-- Each actual mirabolic operator preserves the L² norm. -/
@[simp] theorem norm_mirabolicOperator {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (g : GeneralLinear.mirabolic n F.Carrier) (f : Lp ℂ 2 μ),
        ‖mirabolicOperator F T μ g f‖ = ‖f‖ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ g f
  exact (mirabolicOperator F T μ g).norm_map f

/-- The actual complex representation, obtained by forgetting only the isometry structure. -/
def mirabolicRepresentation {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      Representation ℂ (GeneralLinear.mirabolic n F.Carrier) (Lp ℂ 2 μ) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro _ _ μ _
  exact
    { toFun := fun g => (mirabolicOperator F T μ g).toLinearEquiv.toLinearMap
      map_one' := by
        apply LinearMap.ext
        intro f
        change mirabolicOperator F T μ 1 f = f
        rw [mirabolicOperator_one]
        rfl
      map_mul' := by
        intro g h
        apply LinearMap.ext
        intro f
        change mirabolicOperator F T μ (g * h) f =
          mirabolicOperator F T μ g (mirabolicOperator F T μ h f)
        exact (congrArg (fun e : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ => e f)
          (mirabolicOperator_mul F T μ g h)).symm }

/-- The representation applies the constructed isometry, without changing its carrier. -/
theorem mirabolicRepresentation_apply {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (g : GeneralLinear.mirabolic n F.Carrier) (f : Lp ℂ 2 μ),
        mirabolicRepresentation F T μ g f = mirabolicOperator F T μ g f := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ g f
  rfl

/-- Identity action in the representation. -/
@[simp] theorem mirabolicRepresentation_one_apply {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (f : Lp ℂ 2 μ),
        mirabolicRepresentation F T μ (1 : GeneralLinear.mirabolic n F.Carrier) f = f := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ f
  rw [map_one]
  rfl

/-- Multiplication acts in the left representation order. -/
theorem mirabolicRepresentation_mul_apply {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (g h : GeneralLinear.mirabolic n F.Carrier) (f : Lp ℂ 2 μ),
        mirabolicRepresentation F T μ (g * h) f =
          mirabolicRepresentation F T μ g (mirabolicRepresentation F T μ h f) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ g h f
  rw [map_mul]
  rfl

/-- The representation action has the actual inverse-affine representative. -/
theorem coeFn_mirabolicRepresentation {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (g : GeneralLinear.mirabolic n F.Carrier) (f : Lp ℂ 2 μ),
        mirabolicRepresentation F T μ g f =ᵐ[μ] fun x =>
          NormalizedL2Pullback.normalization (T.determinantNorm n (linearPart g) : ℝ≥0) •
            f (((linearPart g)⁻¹).val.mulVec (x - columnPart g)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ g f
  exact coeFn_mirabolicOperator F T μ g f

/-- On an affine matrix the representation is exactly the affine L² operator. -/
@[simp] theorem mirabolicRepresentation_affineMatrix {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (A : GeneralLinear n F.Carrier) (v : Fin n → F.Carrier) (f : Lp ℂ 2 μ),
        mirabolicRepresentation F T μ (affineMatrix A v) f = operator F T μ A v f := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ A v f
  rw [mirabolicRepresentation_apply, mirabolicOperator_affineMatrix]

/-- The actual representation preserves norms. -/
@[simp] theorem norm_mirabolicRepresentation {n : ℕ} :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace (Fin n → F.Carrier)] [BorelSpace (Fin n → F.Carrier)]
      (μ : Measure (Fin n → F.Carrier)) [Measure.IsAddHaarMeasure μ],
      ∀ (g : GeneralLinear.mirabolic n F.Carrier) (f : Lp ℂ 2 μ),
        ‖mirabolicRepresentation F T μ g f‖ = ‖f‖ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ g f
  exact norm_mirabolicOperator F T μ g f

end Langlands.AffineL2

import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

open Set MeasureTheory MeasureTheory.Measure Matrix
open scoped NNReal ENNReal Kronecker

namespace Langlands.HarmonicAnalysis

section Product
variable {K ι : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [Fintype ι] [DecidableEq ι]
  (ν : Measure K) [SigmaFinite ν] [IsAddLeftInvariant ν]

/-- A shear preserves a finite product of translation-invariant scalar measures. -/
theorem productMeasure_preserving_transvection (t : TransvectionStruct ι K) :
    MeasurePreserving (toLin' t.toMatrix) (Measure.pi fun _ : ι => ν)
      (Measure.pi fun _ : ι => ν) := by
  have ht : Measurable (toLin' t.toMatrix) :=
    (LinearMap.continuous_on_pi _).measurable
  refine ⟨ht, (pi_eq fun s hs => ?_).symm⟩
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ => hs i
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self (μ := ν)
      (fun xᵢ => indicator (univ.pi s) 1 (Function.update x t_i xᵢ))]

variable (χ : K →*₀ ℝ≥0)
  (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)

include hχ

omit [IsAddLeftInvariant ν] in
/-- Coordinatewise scalar change of variables for an invertible diagonal. -/
theorem productMeasure_map_diagonal {D : ι → K} (hD : det (diagonal D) ≠ 0) :
    (Measure.pi fun _ : ι => ν).map (toLin' (diagonal D)) =
      (χ (det (diagonal D)))⁻¹ • (Measure.pi fun _ : ι => ν) := by
  have hDi (i : ι) : D i ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (by simpa only [det_diagonal] using hD) i (Finset.mem_univ i)
  have he (i : ι) (s : Set K) (hs : MeasurableSet s) :
      ν ((fun x => D i * x) ⁻¹' s) = ((χ (D i))⁻¹ : ℝ≥0) • ν s := by
    rw [← map_apply (by fun_prop) hs, hχ _ (hDi i)]
    rfl
  calc
    _ = Measure.pi (fun i : ι => (χ (D i))⁻¹ • ν) := by
      apply (Measure.pi_eq fun s hs => ?_).symm
      rw [Measure.map_apply (LinearMap.continuous_on_pi _).measurable (.univ_pi hs)]
      have hp : (toLin' (diagonal D) ⁻¹' univ.pi s) =
          univ.pi (fun i => (fun x => D i * x) ⁻¹' s i) := by
        ext x
        simp [diagonal_toLin']
      rw [hp, pi_pi]
      simp only [he _ _ (hs _), coe_smul, Pi.smul_apply]
    _ = _ := by
      apply Measure.pi_eq fun s hs => ?_
      simp only [det_diagonal, map_prod, coe_smul, Pi.smul_apply,
        pi_pi, Finset.prod_smul, Finset.prod_inv_distrib]

/-- Scalar change of variables implies determinant change of variables on finite products. -/
theorem productMeasure_map_matrix {M : Matrix ι ι K} (hM : det M ≠ 0) :
    (Measure.pi fun _ : ι => ν).map (toLin' M) =
      (χ (det M))⁻¹ • (Measure.pi fun _ : ι => ν) := by
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD
    exact productMeasure_map_diagonal ν χ hχ hD
  · intro t
    simpa only [TransvectionStruct.det, map_one, inv_one, one_smul] using
      (productMeasure_preserving_transvection ν t).map_eq
  · intro A B _ _ IHA IHB
    rw [toLin'_mul, det_mul, LinearMap.coe_comp, ← Measure.map_map, IHB,
      Measure.map_smul, IHA, smul_smul, map_mul, mul_inv, mul_comm]
    · exact (LinearMap.continuous_on_pi _).measurable.aemeasurable
    · exact (LinearMap.continuous_on_pi _).measurable
    · exact (LinearMap.continuous_on_pi _).measurable

end Product

section Haar
variable {K ι : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [LocallyCompactSpace K]
  [Fintype ι] [DecidableEq ι]
  (ν : Measure K) [IsAddHaarMeasure ν]
  (χ : K →*₀ ℝ≥0)
  (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)

include hχ

/-- The determinant identity transfers from product Haar to every additive Haar measure. -/
theorem haarMeasure_map_matrix (μ : Measure (ι → K)) [IsAddHaarMeasure μ]
    {M : Matrix ι ι K} (hM : det M ≠ 0) :
    μ.map (toLin' M) = (χ (det M))⁻¹ • μ := by
  have hμ := isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : ι => ν)
  rw [hμ, Measure.map_smul, productMeasure_map_matrix ν χ hχ hM, smul_comm]
  exact (LinearMap.continuous_on_pi _).measurable.aemeasurable

/-- Transfer determinant scaling through continuous additive coordinates. -/
theorem haarMeasure_map_in_coordinates
    {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [MeasurableSpace E] [BorelSpace E] (e : E ≃ₜ+ (ι → K))
    (μ : Measure E) [IsAddHaarMeasure μ]
    {M : Matrix ι ι K} (hM : det M ≠ 0) :
    μ.map (fun x => e.symm (toLin' M (e x))) = (χ (det M))⁻¹ • μ := by
  have hm := (LinearMap.continuous_on_pi (toLin' M)).measurable
  have hme : Measurable (e : E → (ι → K)) := e.continuous.measurable
  have hmes : Measurable (e.symm : (ι → K) → E) := e.symm.continuous.measurable
  have h := congrArg (Measure.map e.symm)
    (haarMeasure_map_matrix ν χ hχ (μ.map e) hM)
  rw [Measure.map_smul _ hmes.aemeasurable] at h
  have he : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map hmes hme]
    have hid : (e.symm ∘ e) = (id : E → E) := funext e.symm_apply_apply
    rw [hid]
    exact Measure.map_id
  rw [he, Measure.map_map hmes hm,
    Measure.map_map (hmes.comp hm) hme] at h
  exact h

end Haar

section Rectangular
variable {K m n : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [LocallyCompactSpace K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Entrywise continuous additive coordinates for a rectangular matrix. -/
def rectangularCoordinates : Matrix m n K ≃ₜ+ (m × n → K) where
  toEquiv := (Equiv.curry m n K).symm
  map_add' _ _ := rfl
  continuous_toFun := Homeomorph.piCurry.symm.continuous
  continuous_invFun := Homeomorph.piCurry.continuous

omit [IsTopologicalRing K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [LocallyCompactSpace K] in
/-- In entrywise coordinates, left-right multiplication is a Kronecker matrix. -/
theorem rectangularCoordinates_mul (A : Matrix m m K) (B : Matrix n n K)
    (X : Matrix m n K) :
    rectangularCoordinates (A * X * B) =
      toLin' (A ⊗ₖ B.transpose) (rectangularCoordinates X) := by
  ext ⟨i, j⟩
  change (A * X * B) i j = ((A ⊗ₖ B.transpose).mulVec (Function.uncurry X)) (i, j)
  simp only [mul_apply, mulVec, dotProduct, Fintype.sum_prod_type,
    kronecker_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change A i a * X a b * B b j = A i a * B b j * X a b
  ac_rfl

/-- Determinant change of variables for rectangular matrices and arbitrary Borel Haar measure. -/
theorem haarMeasure_map_rectangular
    (ν : Measure K) [IsAddHaarMeasure ν] (χ : K →*₀ ℝ≥0)
    (hχ : ∀ a : K, a ≠ 0 → ν.map (fun x => a * x) = (χ a)⁻¹ • ν)
    [MeasurableSpace (Matrix m n K)] [BorelSpace (Matrix m n K)]
    (μ : Measure (Matrix m n K)) [IsAddHaarMeasure μ]
    (A : Matrix m m K) (B : Matrix n n K) (hA : det A ≠ 0) (hB : det B ≠ 0) :
    μ.map (fun X => A * X * B) =
      (χ (det A) ^ Fintype.card n * χ (det B) ^ Fintype.card m)⁻¹ • μ := by
  have hM : det (A ⊗ₖ B.transpose) ≠ 0 := by
    rw [det_kronecker, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)
  have h := haarMeasure_map_in_coordinates ν χ hχ rectangularCoordinates μ hM
  have he : (fun x => rectangularCoordinates.symm
      (toLin' (A ⊗ₖ B.transpose) (rectangularCoordinates x))) =
      (fun X => A * X * B) := by
    funext X
    rw [← rectangularCoordinates_mul, ContinuousAddEquiv.symm_apply_apply]
  rw [he, det_kronecker, det_transpose, map_mul, map_pow, map_pow] at h
  exact h

end Rectangular

universe uF

/-- Left and inverse-right multiplication scale every rectangular additive Haar
measure by the inverse residue-normalized determinant quotient. -/
theorem padicRectangularHaarScaling {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (r s : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      [BorelSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      (μ : Measure (Matrix (Fin r) (Fin s) F.Carrier)) [IsAddHaarMeasure μ]
      (A : GeneralLinear r F.Carrier) (B : GeneralLinear s F.Carrier),
      μ.map (fun X => (A : Matrix (Fin r) (Fin r) F.Carrier) * X *
        ((B⁻¹ : GeneralLinear s F.Carrier) : Matrix (Fin s) (Fin s) F.Carrier)) =
        (((T.determinantNorm r A : ℝ≥0) ^ s /
          (T.determinantNorm s B : ℝ≥0) ^ r)⁻¹) • μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro _ _ μ _ A B
  have hχ (a : F.Carrier) (ha : a ≠ 0) :
      (addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • addHaar :=
    padicScalarHaarScaling F T addHaar (Units.mk0 a ha)
  have h := haarMeasure_map_rectangular addHaar T.normalizedAbsHom hχ μ
    (A : Matrix (Fin r) (Fin r) F.Carrier)
    ((B⁻¹ : GeneralLinear s F.Carrier) : Matrix (Fin s) (Fin s) F.Carrier)
    (GeneralLinear.determinant A).ne_zero (GeneralLinear.determinant B⁻¹).ne_zero
  change μ.map _ =
    ((T.determinantNorm r A : ℝ≥0) ^ Fintype.card (Fin s) *
      (T.determinantNorm s B⁻¹ : ℝ≥0) ^ Fintype.card (Fin r))⁻¹ • μ at h
  simpa only [Fintype.card_fin, map_inv, Units.val_inv_eq_inv_val,
    inv_pow, div_eq_mul_inv] using h

/-- Multiplication of every rectangular entry by a field unit has inverse
absolute-value factor to the number of entries, including empty matrices. -/
theorem padicRectangularScalarHaarScaling {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (r s : ℕ) :
    letI := T.topology
    ∀ [MeasurableSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      [BorelSpace (Matrix (Fin r) (Fin s) F.Carrier)]
      (μ : Measure (Matrix (Fin r) (Fin s) F.Carrier)) [IsAddHaarMeasure μ]
      (a : F.Carrierˣ),
      μ.map (β := Matrix (Fin r) (Fin s) F.Carrier)
        (fun X => fun i j => (a : F.Carrier) * X i j) =
        (((T.normalizedAbsUnits a : ℝ≥0) ^ (r * s))⁻¹) • μ := by
  let := T.topology
  intro _ _ μ _ a
  have h := padicRectangularHaarScaling F T r s μ (GeneralLinear.scalar a) 1
  simp only [T.determinantNorm_scalar, Units.val_pow_eq_pow_val, map_one,
    Units.val_one, one_pow, div_one, ← pow_mul, inv_one, Matrix.mul_one] at h
  have he : (fun X : Matrix (Fin r) (Fin s) F.Carrier =>
      ((GeneralLinear.scalar (n := r) a : GeneralLinear r F.Carrier) :
        Matrix (Fin r) (Fin r) F.Carrier) * X) =
      (fun X => ((fun i j => (a : F.Carrier) * X i j) :
        Matrix (Fin r) (Fin s) F.Carrier)) := by
    funext X i j
    exact diagonal_mul (fun _ => (a : F.Carrier)) X i j
  rw [he] at h
  exact h

/-- The exact published rectangular Haar scaling proposition. -/
theorem padicRectangularHaarScalingStatement : PadicRectangularHaarScalingStatement.{uF} := by
  intro p _ F T r s
  exact padicRectangularHaarScaling F T r s

end Langlands.HarmonicAnalysis

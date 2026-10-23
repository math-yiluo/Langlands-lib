import Langlands.HarmonicAnalysis.RowFourier
import Langlands.HarmonicAnalysis.CharacterTransport

/-! # Row Fourier integrals with an explicit row-space measure -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Langlands.HarmonicAnalysis

universe u

section Coordinates

variable {F : Type u} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]
  {d : ℕ}

/-- The product of possibly different scalar Haar measures in the coordinates. -/
def rowCoordinateMeasure (μ : Fin d → AdditiveHaarMeasure F) : Measure (Fin d → F) :=
  Measure.pi (fun i => (μ i).measure)

instance rowCoordinateMeasure_sigmaFinite (μ : Fin d → AdditiveHaarMeasure F)
    [∀ i, SigmaFinite (μ i).measure] : SigmaFinite (rowCoordinateMeasure μ) :=
  inferInstanceAs (SigmaFinite (Measure.pi (fun i => (μ i).measure)))

instance rowCoordinateMeasure_isAddHaar [MeasurableAdd₂ F]
    (μ : Fin d → AdditiveHaarMeasure F) [∀ i, SigmaFinite (μ i).measure] :
    (rowCoordinateMeasure μ).IsAddHaarMeasure :=
  inferInstanceAs (Measure.pi (fun i => (μ i).measure)).IsAddHaarMeasure

instance rowCoordinateMeasure_isFiniteOnCompacts (μ : Fin d → AdditiveHaarMeasure F)
    [∀ i, SigmaFinite (μ i).measure] :
    IsFiniteMeasureOnCompacts (rowCoordinateMeasure μ) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi (fun i => (μ i).measure)))

theorem rowCoordinateMeasure_box (μ : Fin d → AdditiveHaarMeasure F)
    [∀ i, SigmaFinite (μ i).measure] (S : Fin d → Set F) :
    rowCoordinateMeasure μ (Set.univ.pi S) = ∏ i, (μ i).measure (S i) :=
  Measure.pi_pi _ _

@[simp] theorem rowCoordinateMeasure_const (μ : AdditiveHaarMeasure F) (d : ℕ) :
    rowCoordinateMeasure (fun _ : Fin d => μ) = rowMeasure μ d := rfl

variable [IsTopologicalAddGroup F] [BorelSpace F]

/-- Coordinate rescalings affect the product only by their total product.
In particular the individual factors of a fixed row measure need not be fixed. -/
theorem rowCoordinateMeasure_scale (μ : Fin d → AdditiveHaarMeasure F)
    [∀ i, SigmaFinite (μ i).measure] (c : Fin d → NNReal) (hc : ∀ i, 0 < c i) :
    rowCoordinateMeasure (fun i => (μ i).scale (c i) (hc i)) =
      (∏ i, (c i : ℝ≥0∞)) • rowCoordinateMeasure μ := by
  let : ∀ i, SigmaFinite ((μ i).scale (c i) (hc i)).measure := fun i => by
    change SigmaFinite ((c i) • (μ i).measure)
    infer_instance
  apply Measure.pi_eq
  intro S hS
  simp only [AdditiveHaarMeasure.scale_measure, Measure.nnreal_smul_coe_apply,
    Measure.smul_apply, smul_eq_mul, rowCoordinateMeasure_box]
  exact Finset.prod_mul_distrib.symm

theorem rowCoordinateMeasure_scale_of_prod_one (μ : Fin d → AdditiveHaarMeasure F)
    [∀ i, SigmaFinite (μ i).measure] (c : Fin d → NNReal) (hc : ∀ i, 0 < c i)
    (hprod : ∏ i, (c i : ℝ≥0∞) = 1) :
    rowCoordinateMeasure (fun i => (μ i).scale (c i) (hc i)) =
      rowCoordinateMeasure μ := by
  rw [rowCoordinateMeasure_scale, hprod, one_smul]

end Coordinates

section Fourier

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F] {d : ℕ}

/-- The plus-sign row Fourier integral for an actual supplied row-space measure.
For arbitrary functions this uses the usual Bochner nonintegrable convention. -/
def rowFourierIntegralWithMeasure (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (Fin d → F)) (f : (Fin d → F) → ℂ) (y : Fin d → F) : ℂ :=
  ∫ x, ψ.complex (rowPairing x y) * f x ∂μ

omit [IsTopologicalRing F] [BorelSpace F] in
@[simp] theorem rowFourierIntegralWithMeasure_rowMeasure (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (f : (Fin d → F) → ℂ) (y : Fin d → F) :
    rowFourierIntegralWithMeasure ψ (rowMeasure μ d) f y =
      rowFourierIntegral ψ μ d f y := rfl

variable [BorelSpace (Fin d → F)]

omit [BorelSpace F] in
theorem rowFourierIntegrandWithMeasure_integrable (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (Fin d → F)) [IsFiniteMeasureOnCompacts μ]
    (f : SchwartzBruhat (Fin d → F)) (y : Fin d → F) :
    Integrable (fun x => ψ.complex (rowPairing x y) * f x) μ := by
  have hc := (ψ.continuous_complex.comp (continuous_rowPairing_left y)).mul f.continuous
  exact hc.integrable_of_hasCompactSupport f.hasCompactSupport.mul_left

/-- The genuine linear Fourier integral on the test space. -/
def rowFourierTransformWithMeasure (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (Fin d → F)) [IsFiniteMeasureOnCompacts μ] :
    SchwartzBruhat (Fin d → F) →ₗ[ℂ] ((Fin d → F) → ℂ) where
  toFun f := rowFourierIntegralWithMeasure ψ μ f
  map_add' f g := by
    ext y
    change (∫ x, ψ.complex (rowPairing x y) * (f x + g x) ∂μ) =
      (∫ x, ψ.complex (rowPairing x y) * f x ∂μ) +
      ∫ x, ψ.complex (rowPairing x y) * g x ∂μ
    simp_rw [mul_add]
    exact integral_add (rowFourierIntegrandWithMeasure_integrable ψ μ f y)
      (rowFourierIntegrandWithMeasure_integrable ψ μ g y)
  map_smul' c f := by
    ext y
    change (∫ x, ψ.complex (rowPairing x y) * (c * f x) ∂μ) =
      c * ∫ x, ψ.complex (rowPairing x y) * f x ∂μ
    simp_rw [mul_left_comm (ψ.complex _) c]
    exact integral_const_mul c _

omit [BorelSpace F] in
@[simp] theorem rowFourierTransformWithMeasure_rowMeasure
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    [SigmaFinite μ.measure] :
    rowFourierTransformWithMeasure ψ (rowMeasure μ d) = rowFourierTransform ψ μ := by
  ext f y
  rfl

/-- Self-duality is a condition on the whole row measure, including convergence
of the second integral. It does not prescribe individual coordinate measures. -/
def IsRowSelfDualMeasure (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (Fin d → F)) : Prop :=
  ∀ f : SchwartzBruhat (Fin d → F),
    (∀ y : Fin d → F, Integrable
      (fun x => ψ.complex (rowPairing x y) * rowFourierIntegralWithMeasure ψ μ f x) μ) ∧
    ∀ y : Fin d → F,
      rowFourierIntegralWithMeasure ψ μ (rowFourierIntegralWithMeasure ψ μ f) y = f (-y)

omit [IsTopologicalRing F] [BorelSpace F] [BorelSpace (Fin d → F)] in
@[simp] theorem isRowSelfDualMeasure_rowMeasure (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) :
    IsRowSelfDualMeasure ψ (rowMeasure μ d) ↔ IsRowSelfDual ψ μ d := Iff.rfl

omit [MeasurableSpace F] [BorelSpace F] in
/-- Scaling the character by `-1` is exactly conjugation, because it is unitary. -/
theorem complex_scale_neg_one (ψ : UnitaryAdditiveCharacter F) (x : F) :
    (ψ.scale (-1)).complex x = starRingEnd ℂ (ψ.complex x) := by
  change ψ.complex ((↑(-1 : Fˣ) : F) * x) = _
  simp only [Units.val_neg, Units.val_one, neg_one_mul]
  rw [AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (ψ.norm_complex x)

omit [BorelSpace F] [BorelSpace (Fin d → F)] in
/-- Shahidi's conjugate-character kernel is the plus-sign transform for
the inverse character. No additional sign is inserted in the row pairing. -/
theorem rowFourierIntegralWithMeasure_scale_neg_one
    (ψ : UnitaryAdditiveCharacter F) (μ : Measure (Fin d → F))
    (f : (Fin d → F) → ℂ) (y : Fin d → F) :
    rowFourierIntegralWithMeasure (ψ.scale (-1)) μ f y =
      ∫ x, starRingEnd ℂ (ψ.complex (rowPairing x y)) * f x ∂μ := by
  unfold rowFourierIntegralWithMeasure
  simp_rw [complex_scale_neg_one]

omit [BorelSpace F] [BorelSpace (Fin d → F)] in
theorem rowFourierIntegralWithMeasure_scale_neg_one_eq
    (ψ : UnitaryAdditiveCharacter F) (μ : Measure (Fin d → F))
    (f : (Fin d → F) → ℂ) (y : Fin d → F) :
    rowFourierIntegralWithMeasure (ψ.scale (-1)) μ f y =
      rowFourierIntegralWithMeasure ψ μ f (-y) := by
  unfold rowFourierIntegralWithMeasure
  congr 1
  funext x
  congr 1
  change ψ.complex ((↑(-1 : Fˣ) : F) * rowPairing x y) =
    ψ.complex (rowPairing x (-y))
  congr 1
  simp [rowPairing, Finset.sum_neg_distrib]

end Fourier

end Langlands.HarmonicAnalysis

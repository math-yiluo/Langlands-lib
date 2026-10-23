import Langlands.Representation.Shahidi.MeasureTransport
import Langlands.HarmonicAnalysis.RowFourierMeasure
import Langlands.Representation.RankinSelberg.Measures

/-! # Coupled scalar, row and matrix measures in Shahidi's normalization -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Langlands.Shahidi

open HarmonicAnalysis

universe uF

section Matrix

variable {F : Type uF} [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]
  {r s : ℕ}

/-- The product of the actual scalar measures attached to the matrix entries.
The measures in different entries are allowed to differ. -/
def matrixCoordinateMeasure
    (μ : Fin r → Fin s → AdditiveHaarMeasure F) : Measure (Matrix (Fin r) (Fin s) F) :=
  Measure.pi (fun i => rowCoordinateMeasure (μ i))

instance matrixCoordinateMeasure_sigmaFinite
    (μ : Fin r → Fin s → AdditiveHaarMeasure F)
    [∀ i j, SigmaFinite (μ i j).measure] : SigmaFinite (matrixCoordinateMeasure μ) :=
  inferInstanceAs (SigmaFinite (Measure.pi (fun i => rowCoordinateMeasure (μ i))))

instance matrixCoordinateMeasure_isAddHaar [MeasurableAdd₂ F]
    (μ : Fin r → Fin s → AdditiveHaarMeasure F)
    [∀ i j, SigmaFinite (μ i j).measure] :
    (matrixCoordinateMeasure μ).IsAddHaarMeasure :=
  inferInstanceAs (Measure.pi (fun i => rowCoordinateMeasure (μ i))).IsAddHaarMeasure

instance matrixCoordinateMeasure_isFiniteOnCompacts
    (μ : Fin r → Fin s → AdditiveHaarMeasure F)
    [∀ i j, SigmaFinite (μ i j).measure] :
    IsFiniteMeasureOnCompacts (matrixCoordinateMeasure μ) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts
    (Measure.pi (fun i => rowCoordinateMeasure (μ i))))

/-- The mass of a box uses all its actual entry measures. -/
theorem matrixCoordinateMeasure_box
    (μ : Fin r → Fin s → AdditiveHaarMeasure F)
    [∀ i j, SigmaFinite (μ i j).measure] (S : Fin r → Fin s → Set F) :
    matrixCoordinateMeasure μ
        (Set.univ.pi (fun i => Set.univ.pi (S i))) =
      ∏ i, ∏ j, (μ i j).measure (S i j) := by
  change (Measure.pi (fun i => Measure.pi (fun j => (μ i j).measure)))
    (Set.univ.pi (fun i => Set.univ.pi (S i))) = _
  simp only [Measure.pi_pi]

@[simp] theorem matrixCoordinateMeasure_const (μ : AdditiveHaarMeasure F) (r s : ℕ) :
    matrixCoordinateMeasure (fun (_ : Fin r) (_ : Fin s) => μ) =
      RankinSelberg.rectangularMeasure μ r s := rfl

/-- A column factor is a product of the designated coordinate factors.
It is not the pushforward of the full, generally infinite matrix measure
under projection onto that column. -/
def matrixColumnMeasure
    (μ : Fin r → Fin s → AdditiveHaarMeasure F) (j : Fin s) :
    Measure (Fin r → F) :=
  rowCoordinateMeasure (fun i => μ i j)

theorem matrixColumnMeasure_box
    (μ : Fin r → Fin s → AdditiveHaarMeasure F)
    [∀ i j, SigmaFinite (μ i j).measure] (j : Fin s) (S : Fin r → Set F) :
    matrixColumnMeasure μ j (Set.univ.pi S) = ∏ i, (μ i j).measure (S i) :=
  rowCoordinateMeasure_box _ _

/-- Equality of the scalar column factors identifies the actual column
product with the chosen row product. -/
theorem matrixColumnMeasure_eq_rowCoordinateMeasure
    (μ : Fin r → Fin s → AdditiveHaarMeasure F)
    (dx : Fin r → AdditiveHaarMeasure F) (j : Fin s)
    (h : ∀ i, (μ i j).measure = (dx i).measure) :
    matrixColumnMeasure μ j = rowCoordinateMeasure dx := by
  unfold matrixColumnMeasure rowCoordinateMeasure
  congr 1
  funext i
  exact h i

end Matrix

section Compatibility

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [MeasurableSpace Fˣ]
  (n : ℕ)
  [MeasurableSpace (GeneralLinear (n + 1) F)]

/-- The coordinate compatibility in measure items 2, 3 and 5 on pages 76–77.
It is only this part of the normalization, not a predicate asserting all
of Shahidi's suitable-measure conditions or the comparison theorem. -/
def IsCoordinateMeasureCompatible
    (abv : AbsoluteValue F ℝ) (ψ : UnitaryAdditiveCharacter F)
    (dzStar : Measure Fˣ) (dgStar : Measure (GeneralLinear (n + 1) F))
    (dx : Fin (n + 1) → AdditiveHaarMeasure F)
    (da : Fin (n + 1) → Fin (n + 1) → AdditiveHaarMeasure F) : Prop :=
  (dx 0).measure = fieldMeasureFromUnits abv dzStar ∧
  IsRowSelfDualMeasure (ψ.scale (-1)) (rowCoordinateMeasure dx) ∧
  matrixCoordinateMeasure da = matrixMeasureFromGeneralLinear (n + 1) abv dgStar ∧
  ∀ i, (da i 0).measure = (dx i).measure

variable {n}

/-- The top-left scalar measure is the weighted central measure. -/
theorem IsCoordinateMeasureCompatible.corner
    {abv : AbsoluteValue F ℝ} {ψ : UnitaryAdditiveCharacter F}
    {dzStar : Measure Fˣ} {dgStar : Measure (GeneralLinear (n + 1) F)}
    {dx : Fin (n + 1) → AdditiveHaarMeasure F}
    {da : Fin (n + 1) → Fin (n + 1) → AdditiveHaarMeasure F}
    (h : IsCoordinateMeasureCompatible n abv ψ dzStar dgStar dx da) :
    (da 0 0).measure = fieldMeasureFromUnits abv dzStar :=
  (h.2.2.2 0).trans h.1

/-- The first-column factor measure is precisely the chosen Fourier row measure. -/
theorem IsCoordinateMeasureCompatible.firstColumn
    {abv : AbsoluteValue F ℝ} {ψ : UnitaryAdditiveCharacter F}
    {dzStar : Measure Fˣ} {dgStar : Measure (GeneralLinear (n + 1) F)}
    {dx : Fin (n + 1) → AdditiveHaarMeasure F}
    {da : Fin (n + 1) → Fin (n + 1) → AdditiveHaarMeasure F}
    (h : IsCoordinateMeasureCompatible n abv ψ dzStar dgStar dx da) :
    matrixColumnMeasure da 0 = rowCoordinateMeasure dx :=
  matrixColumnMeasure_eq_rowCoordinateMeasure da dx 0 h.2.2.2

/-- Self-duality belongs to that whole column factor, with the source's
conjugate character expressed by the Library's plus-sign transform. -/
theorem IsCoordinateMeasureCompatible.firstColumn_selfDual
    {abv : AbsoluteValue F ℝ} {ψ : UnitaryAdditiveCharacter F}
    {dzStar : Measure Fˣ} {dgStar : Measure (GeneralLinear (n + 1) F)}
    {dx : Fin (n + 1) → AdditiveHaarMeasure F}
    {da : Fin (n + 1) → Fin (n + 1) → AdditiveHaarMeasure F}
    (h : IsCoordinateMeasureCompatible n abv ψ dzStar dgStar dx da) :
    IsRowSelfDualMeasure (ψ.scale (-1)) (matrixColumnMeasure da 0) := by
  rw [h.firstColumn]
  exact h.2.1

end Compatibility

end Langlands.Shahidi

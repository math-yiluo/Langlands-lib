import Langlands.Representation.Shahidi.Geometry
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Map

/-! # Concrete radical measures in Shahidi's equal-rank normalization -/

noncomputable section

open MeasureTheory

namespace Langlands.Shahidi

universe uF

variable {F : Type uF} [Field F]
variable (m n : ℕ)

/-- Extract the upper-right rectangular block of an actual matrix unit. -/
def upperCoordinates (g : GeneralLinear (m + n) F) : Matrix (Fin m) (Fin n) F :=
  fun i j => g (i.castAdd n) (j.natAdd m)

/-- Extract the lower-left rectangular block of an actual matrix unit. -/
def lowerCoordinates (g : GeneralLinear (m + n) F) : Matrix (Fin n) (Fin m) F :=
  fun i j => g (i.natAdd m) (j.castAdd n)

@[simp] theorem upperCoordinates_upper (a : Matrix (Fin m) (Fin n) F) :
    upperCoordinates m n (upper m n F a) = a := by
  ext i j
  exact upper_first_second m n F a i j

@[simp] theorem lowerCoordinates_lower (a : Matrix (Fin n) (Fin m) F) :
    lowerCoordinates m n (lower m n F a) = a := by
  ext i j
  exact lower_second_first m n F a i j

theorem intertwiningUnipotent_equalRanks (a : Matrix (Fin n) (Fin n) F) :
    intertwiningUnipotent n n F a = upper n n F a := by
  apply Units.ext
  ext i j
  change (upper n n F a) (Fin.cast (Nat.add_comm n n) i)
    (Fin.cast (Nat.add_comm n n) j) = _
  simp

section Measures

variable [MeasurableSpace F] [MeasurableSpace (GeneralLinear (m + n) F)]

/-- The supplied rectangular measure carried to the actual upper radical,
viewed as a measure on the ambient group. -/
def upperRadicalMeasure (μ : Measure (Matrix (Fin m) (Fin n) F)) :
    Measure (GeneralLinear (m + n) F) :=
  Measure.map (upper m n F) μ

/-- The supplied rectangular measure carried to the actual lower radical. -/
def lowerRadicalMeasure (μ : Measure (Matrix (Fin n) (Fin m) F)) :
    Measure (GeneralLinear (m + n) F) :=
  Measure.map (lower m n F) μ

/-- The measure on the exchanged upper radical used by the intertwining integral. -/
def intertwiningRadicalMeasure (μ : Measure (Matrix (Fin n) (Fin m) F)) :
    Measure (GeneralLinear (m + n) F) :=
  Measure.map (intertwiningUnipotent m n F) μ

end Measures

section Topology

variable [TopologicalSpace F]

theorem continuous_upperCoordinates :
    Continuous (upperCoordinates (F := F) m n) :=
  continuous_pi fun i => continuous_pi fun j =>
    (GeneralLinear.entry (i.castAdd n) (j.natAdd m)).continuous

theorem continuous_lowerCoordinates :
    Continuous (lowerCoordinates (F := F) m n) :=
  continuous_pi fun i => continuous_pi fun j =>
    (GeneralLinear.entry (i.natAdd m) (j.castAdd n)).continuous

variable [IsTopologicalRing F] [MeasurableSpace F]
  [MeasurableSpace (GeneralLinear (m + n) F)]
  [BorelSpace (GeneralLinear (m + n) F)]

section Upper

variable [BorelSpace (Matrix (Fin m) (Fin n) F)]

/-- Transport followed by actual block extraction recovers the supplied measure. -/
theorem upperRadicalMeasure_coordinates (μ : Measure (Matrix (Fin m) (Fin n) F)) :
    Measure.map (upperCoordinates m n) (upperRadicalMeasure m n μ) = μ := by
  rw [upperRadicalMeasure, Measure.map_map
    (continuous_upperCoordinates m n).measurable (continuous_upper m n F).measurable]
  simp only [Function.comp_def, upperCoordinates_upper, Measure.map_id']

theorem upperRadicalMeasure_injective :
    Function.Injective (upperRadicalMeasure (F := F) m n) := by
  intro μ ν h
  have he := congrArg (Measure.map (upperCoordinates m n)) h
  simpa only [upperRadicalMeasure_coordinates] using he

end Upper

section Lower

variable [BorelSpace (Matrix (Fin n) (Fin m) F)]

theorem lowerRadicalMeasure_coordinates (μ : Measure (Matrix (Fin n) (Fin m) F)) :
    Measure.map (lowerCoordinates m n) (lowerRadicalMeasure m n μ) = μ := by
  rw [lowerRadicalMeasure, Measure.map_map
    (continuous_lowerCoordinates m n).measurable (continuous_lower m n F).measurable]
  simp only [Function.comp_def, lowerCoordinates_lower, Measure.map_id']

theorem lowerRadicalMeasure_injective :
    Function.Injective (lowerRadicalMeasure (F := F) m n) := by
  intro μ ν h
  have he := congrArg (Measure.map (lowerCoordinates m n)) h
  simpa only [lowerRadicalMeasure_coordinates] using he

end Lower

end Topology

section EqualRank

variable [MeasurableSpace F] [MeasurableSpace (GeneralLinear (n + n) F)]

theorem intertwiningRadicalMeasure_equalRanks (μ : Measure (Matrix (Fin n) (Fin n) F)) :
    intertwiningRadicalMeasure n n μ = upperRadicalMeasure n n μ := by
  unfold intertwiningRadicalMeasure upperRadicalMeasure
  congr 1

/-- Items 6 and 7 of the equal-rank measure system: the intertwining radical
uses the matrix measure, and both translated Jacquet functionals use the same
lower-radical measure. All measures and coordinate transports are supplied. -/
def IsEqualRankRadicalMeasureCompatible
    (da μA μJ μJ' : Measure (Matrix (Fin n) (Fin n) F))
    (du dv : Measure (GeneralLinear (n + n) F)) : Prop :=
  du = upperRadicalMeasure n n da ∧
    du = intertwiningRadicalMeasure n n μA ∧
    dv = lowerRadicalMeasure n n μJ ∧
    dv = lowerRadicalMeasure n n μJ'

variable [TopologicalSpace F] [IsTopologicalRing F]
  [BorelSpace (GeneralLinear (n + n) F)]
  [BorelSpace (Matrix (Fin n) (Fin n) F)]

/-- The actual measure equations force the intertwining coordinate measure
to equal the prescribed matrix measure and the two Jacquet measures to agree. -/
theorem IsEqualRankRadicalMeasureCompatible.coordinate_eq
    {da μA μJ μJ' : Measure (Matrix (Fin n) (Fin n) F)}
    {du dv : Measure (GeneralLinear (n + n) F)}
    (h : IsEqualRankRadicalMeasureCompatible n da μA μJ μJ' du dv) :
    μA = da ∧ μJ = μJ' := by
  constructor
  · apply upperRadicalMeasure_injective n n
    rw [← intertwiningRadicalMeasure_equalRanks, ← h.2.1, h.1]
  · apply lowerRadicalMeasure_injective n n
    exact h.2.2.1.symm.trans h.2.2.2

/-- The relation is equivalent to literal coordinate equalities and the
prescribed ambient pushforwards; no extra normalization is hidden in transport. -/
theorem isEqualRankRadicalMeasureCompatible_iff
    (da μA μJ μJ' : Measure (Matrix (Fin n) (Fin n) F))
    (du dv : Measure (GeneralLinear (n + n) F)) :
    IsEqualRankRadicalMeasureCompatible n da μA μJ μJ' du dv ↔
      μA = da ∧ μJ = μJ' ∧
        du = upperRadicalMeasure n n da ∧ dv = lowerRadicalMeasure n n μJ := by
  constructor
  · intro h
    exact ⟨h.coordinate_eq.1, h.coordinate_eq.2, h.1, h.2.2.1⟩
  · rintro ⟨rfl, hJ, rfl, rfl⟩
    exact ⟨rfl, (intertwiningRadicalMeasure_equalRanks n _).symm,
      rfl, congrArg (lowerRadicalMeasure n n) hJ⟩

end EqualRank

end Langlands.Shahidi

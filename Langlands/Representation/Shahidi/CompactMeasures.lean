import Langlands.Group.GL.IntegralSubgroup
import Langlands.Representation.RankinSelberg.Measures
import Langlands.HarmonicAnalysis.RowFourierMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-! # Compact-volume conditions in Shahidi's equal-rank normalization -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Langlands.Shahidi

open HarmonicAnalysis

universe uF

variable {F : Type uF} [Field F]

/-- An ideal of the specified integral subring, viewed as an actual subset
of the field. -/
def idealFieldSet (O : Subring F) (I : Ideal O) : Set F :=
  O.subtype '' (I : Set O)

@[simp] theorem zero_mem_idealFieldSet (O : Subring F) (I : Ideal O) :
    (0 : F) ∈ idealFieldSet O I :=
  ⟨0, I.zero_mem, rfl⟩

theorem idealFieldSet_mono (O : Subring F) {I J : Ideal O} (h : I ≤ J) :
    idealFieldSet O I ⊆ idealFieldSet O J :=
  Set.image_mono h

/-- The literal block conditions in the displayed set on Shahidi's page 76.
The upper-left block is any integral invertible matrix, with no congruence
restriction. The lower-left block belongs to the supplied ideal. -/
def compactNormalizationSet (O : Subring F) (n : ℕ) (I : Ideal O) :
    Set (GeneralLinear (n + 1) F) :=
  {g | (∃ k : GeneralLinear n F,
      k ∈ GeneralLinearGroup.integralSubgroup (Fin n) O ∧
      ∀ i j : Fin n, g i.castSucc j.castSucc = k i j) ∧
    (∀ i : Fin n, g i.castSucc (Fin.last n) ∈ O) ∧
    (∀ j : Fin n, g (Fin.last n) j.castSucc ∈ idealFieldSet O I) ∧
    ∃ a : Fˣ, a ∈ RankinSelberg.integralUnits O ∧
      g (Fin.last n) (Fin.last n) = (a : F)}

theorem compactNormalizationSet_mono (O : Subring F) (n : ℕ)
    {I J : Ideal O} (h : I ≤ J) :
    compactNormalizationSet O n I ⊆ compactNormalizationSet O n J := by
  rintro g ⟨hk, hy, hx, ha⟩
  exact ⟨hk, hy, fun j => idealFieldSet_mono O h (hx j), ha⟩

/-- The test set always contains the identity matrix. -/
theorem one_mem_compactNormalizationSet (O : Subring F) (n : ℕ) (I : Ideal O) :
    (1 : GeneralLinear (n + 1) F) ∈ compactNormalizationSet O n I := by
  refine ⟨⟨1, one_mem _, ?_⟩, ?_, ?_, ⟨1, one_mem _, ?_⟩⟩
  · intro i j
    simp [Matrix.one_apply]
  · intro i
    simp
  · intro j
    change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
      (Fin.last n) j.castSucc ∈ idealFieldSet O I
    simp [ne_of_gt (Fin.castSucc_lt_last j)]
  · simp

/-- The displayed block set as a test subset of the actual compact
integral group. No Haar measure on that group is selected here. -/
def compactNormalizationTest (O : Subring F) (n : ℕ) (I : Ideal O) :
    Set (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O) :=
  Subtype.val ⁻¹' compactNormalizationSet O n I

theorem compactNormalizationTest_mono (O : Subring F) (n : ℕ)
    {I J : Ideal O} (h : I ≤ J) :
    compactNormalizationTest O n I ⊆ compactNormalizationTest O n J :=
  Set.preimage_mono (compactNormalizationSet_mono O n h)

@[simp] theorem one_mem_compactNormalizationTest (O : Subring F) (n : ℕ)
    (I : Ideal O) :
    (1 : GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O) ∈
      compactNormalizationTest O n I :=
  one_mem_compactNormalizationSet O n I

/-- Increasing the exponent decreases the compact normalization test set. -/
theorem compactNormalizationTest_antitone (O : Subring F) [IsLocalRing O] (n : ℕ) :
    Antitone (fun r : ℕ =>
      compactNormalizationTest O n (IsLocalRing.maximalIdeal O ^ r)) := by
  intro r s hrs
  exact compactNormalizationTest_mono O n (Ideal.pow_le_pow_right hrs)

section Measures

variable (O : Subring F) (n : ℕ) [MeasurableSpace F]
  [MeasurableSpace Fˣ] [MeasurableSpace (GeneralLinear n F)]

/-- The product measure in item 2, retaining all three supplied factors. -/
def centralCompactProductMeasure (daStar : Measure (GeneralLinear n F))
    (dn₂ : Measure (Fin n → F)) (dzStar : Measure Fˣ) :
    Measure ((GeneralLinear n F × (Fin n → F)) × Fˣ) :=
  (daStar.prod dn₂).prod dzStar

/-- The compact integration domain in item 2, including rank-one's empty
vector coordinate and rank-zero smaller general linear group. -/
def centralCompactProductSet :
    Set ((GeneralLinear n F × (Fin n → F)) × Fˣ) :=
  ((GeneralLinearGroup.integralSubgroup (Fin n) O : Set (GeneralLinear n F)) ×ˢ
    Set.univ.pi (fun _ : Fin n => (O : Set F))) ×ˢ
      (RankinSelberg.integralUnits O : Set Fˣ)

/-- Item 2 fixes the total product mass, not each of the three masses. -/
def IsCentralCompactNormalized (daStar : Measure (GeneralLinear n F))
    (dn₂ : Measure (Fin n → F)) (dzStar : Measure Fˣ) : Prop :=
  centralCompactProductMeasure n daStar dn₂ dzStar (centralCompactProductSet O n) = 1

theorem centralCompactProductMeasure_mass (daStar : Measure (GeneralLinear n F))
    (dn₂ : Measure (Fin n → F)) (dzStar : Measure Fˣ)
    [SFinite dn₂] [SFinite dzStar] :
    centralCompactProductMeasure n daStar dn₂ dzStar (centralCompactProductSet O n) =
      daStar (GeneralLinearGroup.integralSubgroup (Fin n) O) *
        dn₂ (Set.univ.pi (fun _ : Fin n => (O : Set F))) *
          dzStar (RankinSelberg.integralUnits O) := by
  simp only [centralCompactProductMeasure, centralCompactProductSet, Measure.prod_prod]

theorem isCentralCompactNormalized_iff (daStar : Measure (GeneralLinear n F))
    (dn₂ : Measure (Fin n → F)) (dzStar : Measure Fˣ)
    [SFinite dn₂] [SFinite dzStar] :
    IsCentralCompactNormalized O n daStar dn₂ dzStar ↔
      daStar (GeneralLinearGroup.integralSubgroup (Fin n) O) *
        dn₂ (Set.univ.pi (fun _ : Fin n => (O : Set F))) *
          dzStar (RankinSelberg.integralUnits O) = 1 := by
  unfold IsCentralCompactNormalized
  rw [centralCompactProductMeasure_mass]

variable [TopologicalSpace F] [IsLocalRing O]
  [MeasurableSpace (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O)]

/-- Item 3's compact-group mass equation at a specified positive level.
The source's coordinates 2 through n+1 are indexed by `i.succ`. -/
def IsCompactBlockNormalizedAt
    (dk : Measure (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O))
    (dx : Fin (n + 1) → AdditiveHaarMeasure F) (r : ℕ) : Prop :=
  1 ≤ r ∧
    dk (compactNormalizationTest O n (IsLocalRing.maximalIdeal O ^ r)) =
      ∏ i : Fin n, (dx i.succ).measure
        (idealFieldSet O (IsLocalRing.maximalIdeal O ^ r))

/-- The two compact-volume equations of items 2 and 3 on page 76.
The positive-level equation is required at some level, as in the source.
No existence of a compatible tuple or independence of the level is assumed. -/
def IsCompactVolumeCompatible (daStar : Measure (GeneralLinear n F))
    (dn₂ : Measure (Fin n → F)) (dzStar : Measure Fˣ)
    (dk : Measure (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O))
    (dx : Fin (n + 1) → AdditiveHaarMeasure F) : Prop :=
  IsCentralCompactNormalized O n daStar dn₂ dzStar ∧
    ∃ r, IsCompactBlockNormalizedAt O n dk dx r

omit [MeasurableSpace Fˣ] [MeasurableSpace (GeneralLinear n F)] in
/-- The right side of the compact-group normalization is an actual product
measure of an ideal box in the remaining row coordinates. -/
theorem IsCompactBlockNormalizedAt.rowMass
    {dk : Measure (GeneralLinearGroup.integralSubgroup (Fin (n + 1)) O)}
    {dx : Fin (n + 1) → AdditiveHaarMeasure F} [∀ i, SigmaFinite (dx i).measure]
    {r : ℕ} (h : IsCompactBlockNormalizedAt O n dk dx r) :
    dk (compactNormalizationTest O n (IsLocalRing.maximalIdeal O ^ r)) =
      rowCoordinateMeasure (fun i : Fin n => dx i.succ)
        (Set.univ.pi (fun _ => idealFieldSet O (IsLocalRing.maximalIdeal O ^ r))) := by
  rw [rowCoordinateMeasure_box]
  exact h.2

end Measures

end Langlands.Shahidi

import Langlands.Global.AdelicSubgroupHaarMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Independence of normalized subgroup measures from the initial Haar measure -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal

namespace Langlands.Global.LeftCosetSpace

variable {H : Type u} [Group H] [MeasurableSpace H] (Γ : Subgroup H)

private theorem inv_scaled_mass_cancel (c m : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ⊤) :
    (c * m)⁻¹ * c = m⁻¹ := by
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop), mul_right_comm,
    ENNReal.inv_mul_cancel hc0 hcTop, one_mul]

/-- The same quotient probability normalization survives finite positive Haar scaling. -/
theorem normalizedMeasure_smul (ν : Measure H) (s : Set H) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ⊤) :
    normalizedMeasure Γ (c • ν) s = normalizedMeasure Γ ν s := by
  rw [normalizedMeasure, Measure.smul_apply, smul_eq_mul, quotientMeasure_smul,
    smul_smul, inv_scaled_mass_cancel c (ν s) hc0 hcTop]
  rfl

omit [Group H] in
/-- Simultaneous ambient Haar normalization has the same scaling independence. -/
theorem normalizedAmbientMeasure_smul (ν : Measure H) (s : Set H) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ⊤) :
    ((c • ν) s)⁻¹ • (c • ν) = (ν s)⁻¹ • ν := by
  rw [Measure.smul_apply, smul_eq_mul, smul_smul,
    inv_scaled_mass_cancel c (ν s) hc0 hcTop]

end Langlands.Global.LeftCosetSpace

namespace Langlands.Global.AdelicSubgroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (U : Langlands.GroupScheme.SubgroupFunctor G)
  [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local instance normalizationLocallyCompactSpace : LocallyCompactSpace (adelicPoints F G U) :=
  hclosed.locallyCompactSpace

local instance normalizationPolishSpace : PolishSpace (adelicPoints F G U) :=
  hclosed.polishSpace

/-- Quotient mass normalization beginning with any specified subgroup measure.
Probability laws require genuine nonzero Haar and a compact quotient. -/
def normalizedRationalQuotientHaarMeasureFrom (ν : Measure (adelicPoints F G U)) :
    Measure (RationalQuotient F G U) :=
  LeftCosetSpace.normalizedMeasure (rationalSubgroup F G U) ν
    (LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
      (isDiscrete_rationalSubgroup F G U))

/-- The corresponding ambient measure uses exactly the same inverse quotient mass. -/
def normalizedHaarMeasureFrom (ν : Measure (adelicPoints F G U)) :
    Measure (adelicPoints F G U) :=
  (ν (LeftCosetSpace.fundamentalDomain (rationalSubgroup F G U)
    (isDiscrete_rationalSubgroup F G U)))⁻¹ • ν

/-- Every genuine initial Haar gives exactly the existing normalized quotient measure. -/
theorem normalizedRationalQuotientHaarMeasureFrom_eq
    (ν : Measure (adelicPoints F G U)) [ν.IsHaarMeasure] :
    normalizedRationalQuotientHaarMeasureFrom F G U ν =
      normalizedRationalQuotientHaarMeasure F G U := by
  have hν : ν = (Measure.haarScalarFactor ν (Measure.haar : Measure (adelicPoints F G U)) :
      ℝ≥0∞) • Measure.haar := by
    simpa only [ENNReal.smul_def] using Measure.isMulLeftInvariant_eq_smul ν Measure.haar
  have hc0 : (Measure.haarScalarFactor ν (Measure.haar : Measure (adelicPoints F G U)) :
      ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure ν Measure.haar).ne'
  unfold normalizedRationalQuotientHaarMeasureFrom
  rw [hν, LeftCosetSpace.normalizedMeasure_smul _ _ _ _ hc0 (by simp)]
  unfold normalizedRationalQuotientHaarMeasure quotientMassNormalizer rationalQuotientHaarMeasure
  rw [LeftCosetSpace.haarQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
    LeftCosetSpace.quotientMeasure_univ]
  rfl

/-- The simultaneous normalized ambient Haar is equally independent of its initial choice. -/
theorem normalizedHaarMeasureFrom_eq
    (ν : Measure (adelicPoints F G U)) [ν.IsHaarMeasure] :
    normalizedHaarMeasureFrom F G U ν = normalizedHaarMeasure F G U := by
  have hν : ν = (Measure.haarScalarFactor ν (Measure.haar : Measure (adelicPoints F G U)) :
      ℝ≥0∞) • Measure.haar := by
    simpa only [ENNReal.smul_def] using Measure.isMulLeftInvariant_eq_smul ν Measure.haar
  have hc0 : (Measure.haarScalarFactor ν (Measure.haar : Measure (adelicPoints F G U)) :
      ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure ν Measure.haar).ne'
  unfold normalizedHaarMeasureFrom
  rw [hν, LeftCosetSpace.normalizedAmbientMeasure_smul _ _ _ hc0 (by simp)]
  unfold normalizedHaarMeasure quotientMassNormalizer rationalQuotientHaarMeasure
  rw [LeftCosetSpace.haarQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
    LeftCosetSpace.quotientMeasure_univ]

instance normalizedRationalQuotientHaarMeasureFrom_isProbabilityMeasure
    [CompactSpace (RationalQuotient F G U)]
    (ν : Measure (adelicPoints F G U)) [ν.IsHaarMeasure] :
    IsProbabilityMeasure (normalizedRationalQuotientHaarMeasureFrom F G U ν) := by
  rw [normalizedRationalQuotientHaarMeasureFrom_eq F G U ν]
  exact normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U

end Langlands.Global.AdelicSubgroupPoints

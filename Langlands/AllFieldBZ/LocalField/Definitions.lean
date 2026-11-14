import Langlands.LocalField.LocalFieldArithmetic
import Langlands.LocalField.LocalUniformizer
import Langlands.LocalField.ResidueNormalization
import Langlands.Representation.Plancherel.FieldUnitsTopologyProof
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof

/-!
# Local-field packages of arbitrary characteristic

`LocalFieldPackage` is a field packaged as a structure, with no base field and
no characteristic hypothesis. `LocalFieldPackage.TopologicalData F` is the
published `LocalFieldData F.Carrier`: a supplied topology, valuation and
nonarchimedean local-field certificate. The normalization API (`Integers`,
`residueCardinality`, `ord`, `normalizedAbs`, ...) is that of `LocalFieldData`.

The remaining declarations are the arbitrary-field versions of the few
topological and normalization facts used by the all-field port.
-/

open scoped WithZero Topology

namespace Langlands.AllFieldBZ

universe u

/-- A field packaged as a structure; it plays the role of
`Langlands.PadicField p` with the base field and the prime removed. -/
structure LocalFieldPackage where
  Carrier : Type u
  [field : Field Carrier]

attribute [instance] LocalFieldPackage.field

namespace LocalFieldPackage

/-- Package any field. -/
def ofField (K : Type u) [Field K] : LocalFieldPackage.{u} where
  Carrier := K

/-- A nonarchimedean local-field realization of the packaged field: exactly the
published `LocalFieldData` of the carrier. -/
abbrev TopologicalData (F : LocalFieldPackage.{u}) : Type u := LocalFieldData F.Carrier

namespace TopologicalData

variable {F : LocalFieldPackage.{u}} (T : F.TopologicalData)

/-- The field is Hausdorff for the topology of this supplied realization. -/
theorem fieldT2 :
    letI := T.topology
    T2Space F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact HarmonicAnalysis.GeneralLocalField.t2Space F.Carrier

include T in
/-- A nonarchimedean local field is infinite: the powers of a uniformizer have pairwise
distinct valuations. -/
theorem infinite : Infinite F.Carrier := by
  refine Infinite.of_injective
    (fun n : ℕ => LocalFieldData.uniformizer T ^ n) fun a b hab => ?_
  have h : LocalFieldData.ord T (LocalFieldData.uniformizer T ^ a) =
      LocalFieldData.ord T (LocalFieldData.uniformizer T ^ b) :=
    congrArg (LocalFieldData.ord T) hab
  have ha := LocalFieldData.ord_zpow T (LocalFieldData.uniformizer T) (a : ℤ)
  have hb := LocalFieldData.ord_zpow T (LocalFieldData.uniformizer T) (b : ℤ)
  rw [zpow_natCast, LocalFieldData.ord_uniformizer, mul_one] at ha hb
  rw [ha, hb] at h
  exact_mod_cast h

/-- The normalized absolute value vanishes exactly at zero. -/
theorem normalizedAbs_eq_zero_iff (x : F.Carrier) :
    T.normalizedAbs x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (T.normalizedAbs_pos hx).ne' h
  · rintro rfl
    exact T.normalizedAbs_zero

/-- An element is integral exactly when its normalized absolute value is at most one. -/
theorem normalizedAbs_le_one_iff_mem_integers (x : F.Carrier) :
    T.normalizedAbs x ≤ 1 ↔ x ∈ T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  have h := T.normalizedAbs_le_iff_of_ne_zero hx (one_ne_zero : (1 : F.Carrier) ≠ 0)
  rw [T.normalizedAbs_one, map_one] at h
  rw [h]
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier x) ≤ 1 ↔
    ValuativeRel.valuation F.Carrier x ≤ 1
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).strictMono.le_iff_le

/-- The normalized absolute value of the data is the published residue-normalized
absolute value of the same valuation. -/
theorem residueNormalizedAbsoluteValue_eq_normalizedAbs (x : F.Carrier) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    LocalField.residueNormalizedAbsoluteValue F.Carrier x = T.normalizedAbs x := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  by_cases hx : x = 0
  · subst x
    rw [map_zero, T.normalizedAbs_zero]
  · rw [LocalField.residueNormalizedAbsoluteValue_of_ne_zero F.Carrier hx,
      T.normalizedAbs_of_ne_zero hx]
    simp only [LocalFieldData.ord, neg_neg]
    rfl

/-- The normalized absolute value is continuous, including at zero. -/
theorem continuous_normalizedAbs :
    letI := T.topology
    Continuous T.normalizedAbs := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have h : (T.normalizedAbs : F.Carrier → ℝ) =
      fun x => LocalField.residueNormalizedAbsoluteValue F.Carrier x :=
    funext fun x => (T.residueNormalizedAbsoluteValue_eq_normalizedAbs x).symm
  rw [h]
  exact Plancherel.continuous_residueNormalizedAbsoluteValue F.Carrier

/-- Small normalized absolute value forces membership in any neighborhood of zero. -/
theorem exists_normalizedAbs_lt_subset {U : Set F.Carrier}
    (hU : letI := T.topology; U ∈ 𝓝 (0 : F.Carrier)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : F.Carrier, T.normalizedAbs x < ε → x ∈ U := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  obtain ⟨γ, hγ0, hγ⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F.Carrier).mem_iff.mp hU
  obtain ⟨x₀, hx₀⟩ := ValuativeRel.valuation_surjective (K := F.Carrier) γ
  have hx₀0 : x₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hx₀
    exact hγ0 hx₀.symm
  refine ⟨T.normalizedAbs x₀, T.normalizedAbs_pos hx₀0, fun x hx => hγ ?_⟩
  change ValuativeRel.valuation F.Carrier x < γ
  rw [← hx₀]
  by_cases hx0 : x = 0
  · rw [hx0, map_zero]
    exact (ValuativeRel.valuation F.Carrier).pos_iff.mpr hx₀0
  have hle := T.normalizedAbs_le_iff_of_ne_zero hx₀0 hx0
  have hlt : ¬ T.discreteValuation x₀ ≤ T.discreteValuation x := fun h =>
    (not_le.mpr hx) (hle.mpr h)
  rw [not_le] at hlt
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier x) <
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier x₀) at hlt
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).strictMono.lt_iff_lt.mp
    hlt

end TopologicalData

end LocalFieldPackage

end Langlands.AllFieldBZ

import Langlands.LocalField.PadicResidueNormalization
import Langlands.LocalField.Canonical

/-! # A common consumer of the residue-normalized local-field API -/

universe u

namespace Langlands.LocalField

/-- The residue field of `F` has `q > 1` elements, and the integer powers of every
element of source-standard order one have normalized absolute value `q ^ (-n)`. -/
def NormalizedAt (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (q : ℕ) : Prop :=
  residueCardinality F = q ∧ 1 < q ∧
    ∀ π : F, FML.ord F π = 1 → ∀ n : ℤ,
      residueNormalizedAbsoluteValue F (π ^ n) = (q : ℝ) ^ (-n)

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Integer powers of an order-one element. -/
theorem residueNormalizedAbsoluteValue_zpow_of_ord_one {π : F} (hπ : FML.ord F π = 1)
    (n : ℤ) :
    residueNormalizedAbsoluteValue F (π ^ n) = (residueCardinality F : ℝ) ^ (-n) := by
  rw [map_zpow₀, residueNormalizedAbsoluteValue_of_ord_one F hπ, inv_zpow']

/-- Every nonarchimedean local field is normalized at its actual residue cardinality. -/
theorem normalizedAt_residueCardinality : NormalizedAt F (residueCardinality F) :=
  ⟨rfl, residueCardinality_gt_one F,
    fun _ hπ n => residueNormalizedAbsoluteValue_zpow_of_ord_one F hπ n⟩

/-- The consumer is determined by the residue cardinality. -/
theorem normalizedAt_iff (q : ℕ) : NormalizedAt F q ↔ residueCardinality F = q := by
  refine ⟨fun h => h.1, fun h => ?_⟩
  subst h
  exact normalizedAt_residueCardinality F

/-- The chosen uniformizer of a field normalized at `q` has absolute value `q⁻¹`. -/
theorem NormalizedAt.residueNormalizedAbsoluteValue_uniformizer {q : ℕ} (h : NormalizedAt F q) :
    residueNormalizedAbsoluteValue F (uniformizer F) = (q : ℝ)⁻¹ := by
  simpa using h.2.2 (uniformizer F) (ord_uniformizer F) 1

end Langlands.LocalField

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- Every supplied p-adic realization instantiates the common consumer at its host
residue cardinality. -/
theorem normalizedAt :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    LocalField.NormalizedAt F.Carrier T.residueCardinality := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [← T.general_residueCardinality_eq]
  exact LocalField.normalizedAt_residueCardinality F.Carrier

/-- The host normalized absolute value of integer powers of an order-one element. -/
theorem normalizedAbs_zpow_of_ord_one {π : F.Carrier}
    (hπ : letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      FML.ord F.Carrier π = 1) (n : ℤ) :
    T.normalizedAbs (π ^ n) = (T.residueCardinality : ℝ) ^ (-n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [← T.residueNormalizedAbsoluteValue_eq_normalizedAbs]
  exact (T.normalizedAt).2.2 π hπ n

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField

variable {p : ℕ} [Fact p.Prime]

/-- The published canonical realization of an arbitrary `PadicField` instantiates the
common consumer. -/
theorem canonical_normalizedAt (F : PadicField.{u} p) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    LocalField.NormalizedAt F.Carrier F.canonicalTopologicalData.residueCardinality :=
  F.canonicalTopologicalData.normalizedAt

end Langlands.PadicField

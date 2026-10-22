import Langlands.LocalField.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.NormedValued

open scoped NNReal

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime]

/-- The nonnegative-real valuation associated to the base-extending spectral norm. -/
noncomputable def canonicalValuation (F : PadicField.{u} p) :
    Valuation F.Carrier ℝ≥0 := by
  letI := F.canonicalNormedField
  letI : IsUltrametricDist F.Carrier :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
  exact NormedField.valuation

/-- The valuative comparison induced by the spectral valuation. -/
@[instance_reducible]
noncomputable def canonicalValuativeRel (F : PadicField.{u} p) :
    ValuativeRel F.Carrier :=
  ValuativeRel.ofValuation F.canonicalValuation

/-- The canonical local-field realization of every finite extension of `Padic p`. -/
noncomputable def canonicalTopologicalData (F : PadicField.{u} p) :
    F.TopologicalData := by
  letI := F.canonicalNormedField
  letI := F.canonicalNormedAlgebra
  letI : IsUltrametricDist F.Carrier :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
  letI := F.canonicalValuativeRel
  letI : F.canonicalValuation.Compatible := Valuation.Compatible.ofValuation _
  letI : IsValuativeTopology F.Carrier :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle F.canonicalValuation
      (fun {_} => (NormedField.toValued (K := F.Carrier)).is_topological_valuation _)
  letI : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier
  letI : ValuativeRel.IsNontrivial F.Carrier :=
    (ValuativeRel.isNontrivial_iff_isNontrivial F.canonicalValuation).mpr
      (inferInstanceAs (NormedField.valuation (K := F.Carrier)).IsNontrivial)
  refine
    { topology := inferInstance
      valuativeRel := F.canonicalValuativeRel
      valuativeExtension := ?_
      moduleTopology := isModuleTopologyOfFiniteDimensional
      localField := {} }
  constructor
  intro a b
  change ‖algebraMap (Padic p) F.Carrier a‖₊ ≤ ‖algebraMap (Padic p) F.Carrier b‖₊ ↔
    Padic.mulValuation a ≤ Padic.mulValuation b
  rw [← NNReal.coe_le_coe]
  change spectralNorm (Padic p) F.Carrier _ ≤ spectralNorm (Padic p) F.Carrier _ ↔ _
  rw [spectralNorm_extends, spectralNorm_extends]
  simp only [← not_lt, Padic.norm_lt_norm_iff_mulValuation_lt]

end Langlands.PadicField

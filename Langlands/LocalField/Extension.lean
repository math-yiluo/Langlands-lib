import Langlands.Galois.Local.SpectralDefinitions
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Local-field realizations over a specified base

The supplied realization and the spectral constructor are independent of
characteristic. The base norm must induce its supplied valuative comparison.
-/

open scoped NNReal

namespace Langlands.LocalField

universe u₀ uL

/-- A local-field realization of an extension with its base module topology. -/
structure TopologicalData (K₀ : Type u₀) (L : Type uL) [Field K₀]
    [ValuativeRel K₀] [TopologicalSpace K₀] [Field L] [Algebra K₀ L] where
  [topology : TopologicalSpace L]
  [valuativeRel : ValuativeRel L]
  [valuativeExtension : ValuativeExtension K₀ L]
  [moduleTopology : IsModuleTopology K₀ L]
  [localField : IsNonarchimedeanLocalField L]

namespace TopologicalData

variable {K₀ : Type u₀} {L : Type uL} [Field K₀] [ValuativeRel K₀]
  [TopologicalSpace K₀] [Field L] [Algebra K₀ L] (T : TopologicalData K₀ L)

/-- The integer ring of the supplied valuation, without a normalization choice. -/
noncomputable abbrev Integers :=
  letI := T.valuativeRel
  (ValuativeRel.valuation L).integer

/-- The residue field of that actual integer ring. -/
abbrev ResidueField := IsLocalRing.ResidueField T.Integers

/-- The residue quotient of the supplied integer ring. -/
noncomputable abbrev residue : T.Integers →+* T.ResidueField :=
  IsLocalRing.residue T.Integers

end TopologicalData

section Spectral

variable (K₀ : Type u₀) (L : Type uL) [NontriviallyNormedField K₀]
  [IsUltrametricDist K₀] [CompleteSpace K₀] [Field L] [Algebra K₀ L]
  [FiniteDimensional K₀ L]

/-- The norm extending the chosen base norm. -/
noncomputable def canonicalNorm : L → ℝ := spectralNorm K₀ L

/-- The spectral normed field, supplied explicitly rather than as an instance. -/
noncomputable abbrev canonicalNormedField : NontriviallyNormedField L :=
  spectralNorm.nontriviallyNormedField K₀ L

/-- The compatible spectral normed algebra. -/
noncomputable abbrev canonicalNormedAlgebra :
    letI := canonicalNormedField K₀ L
    NormedAlgebra K₀ L :=
  spectralNorm.normedAlgebra K₀ L

/-- The base module topology on the finite extension. -/
noncomputable abbrev canonicalTopology : TopologicalSpace L := moduleTopology K₀ L

/-- The nonnegative-real valuation of the base-extending spectral norm. -/
noncomputable def canonicalValuation : Valuation L ℝ≥0 :=
  Langlands.LocalGalois.spectralValuation K₀ L

/-- The valuative comparison of the spectral valuation. -/
@[instance_reducible]
noncomputable def canonicalValuativeRel : ValuativeRel L :=
  ValuativeRel.ofValuation (canonicalValuation K₀ L)

open ValuativeRel in
/-- The spectral local-field realization over a locally compact base whose
norm comparisons agree with its specified valuative relation. -/
noncomputable def canonicalTopologicalData [ValuativeRel K₀] [LocallyCompactSpace K₀]
    (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ a ≤ᵥ b) : TopologicalData K₀ L := by
  letI := canonicalNormedField K₀ L
  letI := canonicalNormedAlgebra K₀ L
  letI : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := K₀) (L := L))
  letI := canonicalValuativeRel K₀ L
  letI : (canonicalValuation K₀ L).Compatible := Valuation.Compatible.ofValuation _
  letI : IsValuativeTopology L :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle (canonicalValuation K₀ L)
      (fun {_} => (NormedField.toValued (K := L)).is_topological_valuation _)
  letI : ProperSpace L := FiniteDimensional.proper K₀ L
  letI : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial (canonicalValuation K₀ L)).mpr
      (inferInstanceAs (NormedField.valuation (K := L)).IsNontrivial)
  refine
    { topology := inferInstance
      valuativeRel := canonicalValuativeRel K₀ L
      valuativeExtension := ?_
      moduleTopology := isModuleTopologyOfFiniteDimensional
      localField := {} }
  constructor
  intro a b
  change ‖algebraMap K₀ L a‖₊ ≤ ‖algebraMap K₀ L b‖₊ ↔ a ≤ᵥ b
  rw [← NNReal.coe_le_coe]
  change spectralNorm K₀ L _ ≤ spectralNorm K₀ L _ ↔ _
  rw [spectralNorm_extends, spectralNorm_extends]
  exact hbase a b

end Spectral
end Langlands.LocalField

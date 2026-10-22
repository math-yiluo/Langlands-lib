import Langlands.LocalField.CanonicalStatement

open scoped NNReal ValuativeRel

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime]

theorem canonicalTopologicalData_topology (F : PadicField.{u} p) :
    F.canonicalTopologicalData.topology = F.canonicalTopology := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.moduleTopology
  exact eq_moduleTopology (Padic p) F.Carrier

theorem canonicalTopologicalData_normTopology (F : PadicField.{u} p) :
    F.canonicalTopologicalData.topology =
      F.canonicalNormedField.toUniformSpace.toTopologicalSpace := rfl

theorem canonicalValuation_coe (F : PadicField.{u} p) (x : F.Carrier) :
    (F.canonicalValuation x : ℝ) = F.canonicalNorm x := rfl

theorem canonicalValuation_compatible (F : PadicField.{u} p) :
    letI := F.canonicalTopologicalData.valuativeRel
    F.canonicalValuation.Compatible :=
  Valuation.Compatible.ofValuation _

theorem canonicalTopologicalData_vle (F : PadicField.{u} p) (x y : F.Carrier) :
    @ValuativeRel.vle F.Carrier _ F.canonicalTopologicalData.valuativeRel x y ↔
      F.canonicalNorm x ≤ F.canonicalNorm y := by
  change F.canonicalValuation x ≤ F.canonicalValuation y ↔ _
  exact NNReal.coe_le_coe.symm

theorem canonicalNorm_algebraMap (F : PadicField.{u} p) (a : Padic p) :
    F.canonicalNorm (algebraMap (Padic p) F.Carrier a) = ‖a‖ :=
  spectralNorm_extends a

theorem canonicalNorm_prime (F : PadicField.{u} p) :
    F.canonicalNorm (p : F.Carrier) = (p : ℝ)⁻¹ := by
  simpa only [map_natCast, Padic.norm_p] using F.canonicalNorm_algebraMap (p : Padic p)

theorem canonicalTopologicalData_base_vle (F : PadicField.{u} p) (a b : Padic p) :
    @ValuativeRel.vle F.Carrier _ F.canonicalTopologicalData.valuativeRel
      (algebraMap (Padic p) F.Carrier a) (algebraMap (Padic p) F.Carrier b) ↔
        Padic.mulValuation a ≤ Padic.mulValuation b := by
  rw [F.canonicalTopologicalData_vle, F.canonicalNorm_algebraMap, F.canonicalNorm_algebraMap]
  simp only [← not_lt, Padic.norm_lt_norm_iff_mulValuation_lt]

theorem canonical_complete_proper (F : PadicField.{u} p) :
    letI := F.canonicalNormedField
    CompleteSpace F.Carrier ∧ ProperSpace F.Carrier := by
  let := F.canonicalNormedField
  let := F.canonicalNormedAlgebra
  exact ⟨FiniteDimensional.complete (Padic p) F.Carrier,
    FiniteDimensional.proper (Padic p) F.Carrier⟩

theorem canonical_localField_properties (F : PadicField.{u} p) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    LocallyCompactSpace F.Carrier ∧
      CompactSpace 𝒪[F.Carrier] ∧ IsDiscreteValuationRing 𝒪[F.Carrier] ∧
      ValuativeRel.IsDiscrete F.Carrier ∧ Finite 𝓀[F.Carrier] := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem canonical_rational_topology :
    (rational p).canonicalTopologicalData.topology =
      (rationalTopologicalData p).topology := by
  rw [(rational p).canonicalTopologicalData_topology]
  exact (eq_moduleTopology (Padic p) (Padic p)).symm

theorem canonical_rational_vle (a b : Padic p) :
    @ValuativeRel.vle (Padic p) _ (rational p).canonicalTopologicalData.valuativeRel a b ↔
      @ValuativeRel.vle (Padic p) _ (rationalTopologicalData p).valuativeRel a b := by
  exact (rational p).canonicalTopologicalData_base_vle a b

theorem canonicalCompatibility :
    CanonicalCompatibilityStatement.{u} (p := p) := by
  refine ⟨?_, canonical_rational_topology, canonical_rational_vle⟩
  intro F
  exact ⟨F.canonicalTopologicalData_topology, F.canonicalTopologicalData_normTopology,
    F.canonicalValuation_coe, F.canonicalValuation_compatible,
    F.canonicalTopologicalData_vle, F.canonicalNorm_algebraMap,
    F.canonicalNorm_prime, F.canonicalTopologicalData_base_vle, F.canonical_complete_proper,
    F.canonical_localField_properties⟩

end Langlands.PadicField

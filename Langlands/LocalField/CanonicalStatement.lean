import Langlands.LocalField.Canonical

open scoped NNReal ValuativeRel

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Topology, valuation, and local-field consequences of the canonical realization. -/
def CanonicalCompatibilityStatement : Prop :=
  (∀ F : PadicField.{u} p,
    F.canonicalTopologicalData.topology = F.canonicalTopology ∧
    F.canonicalTopologicalData.topology =
      F.canonicalNormedField.toUniformSpace.toTopologicalSpace ∧
    (∀ x : F.Carrier, (F.canonicalValuation x : ℝ) = F.canonicalNorm x) ∧
    (letI := F.canonicalTopologicalData.valuativeRel
     F.canonicalValuation.Compatible) ∧
    (∀ x y : F.Carrier,
      @ValuativeRel.vle F.Carrier _ F.canonicalTopologicalData.valuativeRel x y ↔
        F.canonicalNorm x ≤ F.canonicalNorm y) ∧
    (∀ a : Padic p, F.canonicalNorm (algebraMap (Padic p) F.Carrier a) = ‖a‖) ∧
    F.canonicalNorm (p : F.Carrier) = (p : ℝ)⁻¹ ∧
    (∀ a b : Padic p,
      @ValuativeRel.vle F.Carrier _ F.canonicalTopologicalData.valuativeRel
        (algebraMap (Padic p) F.Carrier a) (algebraMap (Padic p) F.Carrier b) ↔
          Padic.mulValuation a ≤ Padic.mulValuation b) ∧
    (letI := F.canonicalNormedField
     CompleteSpace F.Carrier ∧ ProperSpace F.Carrier) ∧
    (letI := F.canonicalTopologicalData.topology
     letI := F.canonicalTopologicalData.valuativeRel
     LocallyCompactSpace F.Carrier ∧
       CompactSpace 𝒪[F.Carrier] ∧ IsDiscreteValuationRing 𝒪[F.Carrier] ∧
       ValuativeRel.IsDiscrete F.Carrier ∧ Finite 𝓀[F.Carrier])) ∧
  (rational p).canonicalTopologicalData.topology = (rationalTopologicalData p).topology ∧
  (∀ a b : Padic p,
    @ValuativeRel.vle (Padic p) _ (rational p).canonicalTopologicalData.valuativeRel a b ↔
      @ValuativeRel.vle (Padic p) _ (rationalTopologicalData p).valuativeRel a b)

end Langlands.PadicField

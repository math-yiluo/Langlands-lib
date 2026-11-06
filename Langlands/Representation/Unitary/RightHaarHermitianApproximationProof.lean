import Langlands.Representation.Unitary.RightHaarHermitianApproximationStatement
import Langlands.Representation.Unitary.IntegratedHermitianApproximationProof
import Langlands.Analysis.Local.HaarInversionDensityProof

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology

universe uG uE

/-- Specialize continuous Hermitian approximation to the actual right Haar
measure, deriving the density and orbit measurability. -/
theorem rightHaarHermitianApproximation :
    RightHaarHermitianApproximationStatement.{uG, uE} := by
  intro G _ _ _ _ _ _ _ _ E _ _ _ μ _ π hπinner hπcont
  let d : G →* ℝ≥0 :=
    { toFun := fun g => modularCharacter g⁻¹
      map_one' := by simp
      map_mul' := by
        intro g h
        simp only [mul_inv_rev, map_mul, mul_comm] }
  have hd : Continuous d :=
    Langlands.Haar.continuous_modularCharacter_of_locallyCompact.comp continuous_inv
  have hμ : μ.inv.inv = μ.inv.withDensity (fun g => (d g : ℝ≥0∞)) := by
    change μ.inv.inv =
      μ.inv.withDensity (fun g => (modularCharacter g⁻¹ : ℝ≥0∞))
    rw [Measure.inv_inv]
    exact (Langlands.Haar.haarInversionDensity G μ).2
  exact integratedHermitianApproximation μ.inv d hd hμ π hπinner
    (fun x => (hπcont x).stronglyMeasurable.aestronglyMeasurable)
    (fun x => (hπcont x).continuousAt)

end Langlands.Analysis

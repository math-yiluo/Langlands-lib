import Langlands.Representation.Unitary.IntegratedHermitianApproximationStatement
import Langlands.Representation.Unitary.HermitianWeightSequenceProof
import Langlands.Representation.Unitary.IntegratedUnitarySymmetryProof
import Langlands.Representation.Unitary.IntegratedIsometricApproximationProof
import Langlands.Representation.Unitary.IntegratedIsometricNaturalityProof

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal Topology

universe uG uE

/-- Assemble the actual symmetric contraction approximation and naturality. -/
theorem integratedHermitianApproximation :
    IntegratedHermitianApproximationStatement.{uG, uE} := by
  intro G _ _ _ _ _ _ _ _ E _ _ _ μ _ _ d hd hμ π hπinner hπmeas hπcont
  let hπnorm : ∀ (g : G) (x : E), ‖π g x‖ = ‖x‖ :=
    fun g => (LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπinner g)
  obtain ⟨f, hf, hsupp⟩ := hermitianWeightSequence μ d hd
  let hint : ∀ n, Integrable (f n) μ := fun n => (hf n).2.2.2.1
  have hnonneg : ∀ n g, 0 ≤ f n g := fun n => (hf n).2.2.1
  have hmass : ∀ n, ∫ g, f n g ∂μ = 1 := fun n => (hf n).2.2.2.2.1
  have hhermitian : ∀ n g, f n g = (d g : ℝ) * f n g⁻¹ :=
    fun n => (hf n).2.2.2.2.2
  refine ⟨f, hint, ?_, hsupp, ?_⟩
  · exact fun n => ⟨(hf n).1, (hf n).2.1, hnonneg n, hmass n, hhermitian n⟩
  · dsimp only
    refine ⟨?_, ?_, ?_⟩
    · intro n
      constructor
      · apply integratedUnitarySymmetry μ π hπinner hπmeas d hd.measurable hμ
          (fun g => (f n g : ℂ)) (hint n).ofReal
        exact Eventually.of_forall (fun g => by
          simpa only [Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal] using
            congrArg (fun r : ℝ => (r : ℂ)) (hhermitian n g))
      · calc
          ‖integratedIsometricAction μ π hπnorm hπmeas
              (fun g => (f n g : ℂ)) (hint n).ofReal‖ ≤
              ∫ g, ‖(f n g : ℂ)‖ ∂μ :=
            integratedIsometricAction_norm_le μ π hπnorm hπmeas _ _
          _ = 1 := by
            simpa only [Complex.norm_real, Real.norm_of_nonneg (hnonneg n _)] using hmass n
    · apply integratedIsometricApproximation μ π hπnorm hπmeas hπcont f hint hnonneg hmass
      intro U hU
      filter_upwards [hsupp U hU] with n hn
      exact (subset_tsupport (f n)).trans hn
    · intro P hPc hPi
      have hnat := fun n => integratedIsometricNaturality μ π hπnorm hπmeas
        (fun g => (f n g : ℂ)) (hint n).ofReal P hPc hPi
      choose hAP hU using hnat
      exact ⟨hAP, fun Q U hintertwine n => hU n Q U hintertwine⟩

end Langlands.Analysis

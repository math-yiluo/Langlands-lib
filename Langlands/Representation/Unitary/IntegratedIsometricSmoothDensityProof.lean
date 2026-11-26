import Langlands.Analysis.SmoothInverseKernelSequenceProof
import Langlands.Representation.Unitary.IntegratedIsometricApproximationProof
import Langlands.Representation.Unitary.IntegratedIsometricSmoothDensityStatement
import Langlands.Representation.Unitary.IntegratedIsometricSmoothVectorsProof

/-! # Density of smooth vectors by integrated approximation -/

set_option autoImplicit false

universe uV uG uE

namespace Langlands.Analysis

open Filter MeasureTheory
open scoped ContDiff Manifold Topology

/-- Inverse-normalized smooth kernels give smooth vectors converging in norm to each
vector of the original action. -/
theorem integratedIsometricSmoothDensity :
    IntegratedIsometricSmoothDensityStatement.{uV, uG, uE} := by
  intro V _ _ _ G _ _ _ _ _ _ _ _ E _ _ _ μ _ _ _ π hNorm hMeas hCont
  let : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace V G
  obtain ⟨κ, hκ, hSupport⟩ := smoothInverseKernelSequence V G μ
  simp only [forall_and] at hκ
  obtain ⟨hSmooth, hCompact, hNonneg, _, hIntegrable, hMass⟩ := hκ
  let f (n : ℕ) (g : G) := κ n g⁻¹
  have hConcentrates (U : Set G) (hU : U ∈ 𝓝 (1 : G)) :
      ∀ᶠ n in atTop, Function.support (f n) ⊆ U :=
    (hSupport U hU).mono fun n hn => (subset_tsupport (f n)).trans hn.2
  have hConverges := integratedIsometricApproximation μ π hNorm hMeas
    (fun x => (hCont x).continuousAt) f hIntegrable
    (fun n g => hNonneg n g⁻¹) hMass hConcentrates
  intro x
  refine mem_closure_of_tendsto (hConverges x) (Eventually.of_forall fun n => ?_)
  have hComplexSmooth : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℂ) ∞ (fun g => (κ n g : ℂ)) :=
    Complex.ofRealCLM.contDiff.contMDiff.comp (hSmooth n)
  have hComplexCompact : HasCompactSupport (fun g => (κ n g : ℂ)) :=
    (hCompact n).comp_left Complex.ofReal_zero
  exact (integratedIsometricSmoothVectors V G E μ π hNorm hMeas hCont _
    hComplexSmooth hComplexCompact).2 (hIntegrable n).ofReal x

end Langlands.Analysis

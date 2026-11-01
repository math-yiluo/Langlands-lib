import Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierData
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof

/-! Schwartz–Bruhat closure of the actual first-block partial Fourier integral. -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

universe u

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] {a b N : ℕ}
variable (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  [SigmaFinite μ.measure] (hsd : IsSelfDual ψ μ)
  (e : Fin a ⊕ Fin b ≃ Fin N)

include hsd

/-- Finite joined-tensor expansion and self-dual row Fourier closure realize the
actual first-block partial Fourier integral as a full-row Schwartz–Bruhat function. -/
theorem exists_partialFourierSchwartz (Φ : SchwartzBruhat (Fin N → K)) :
    ∃ Ψ : SchwartzBruhat (Fin N → K),
      ∀ ξ v, Ψ (join e ξ v) = rowPartialFourierIntegral ψ μ e Φ ξ v := by
  classical
  obtain ⟨M, α, β, -, hΦ⟩ := exists_rowPartialFourierIntegral_expansion ψ μ e Φ
  have hclosed := (rowFourierCompatibility ψ μ a hsd).1
  choose αhat hαhat using fun j : Fin M => hclosed (α j)
  refine ⟨∑ j, joinedTensor e (αhat j) (β j), ?_⟩
  intro ξ v
  rw [hΦ]
  simp only [Submodule.coe_sum, Finset.sum_apply, joinedTensor_join]
  exact Finset.sum_congr rfl fun j _ => congrArg (fun z => z * β j v) (hαhat j ξ)

/-- The Schwartz–Bruhat function whose values are the actual supplied-measure
plus-sign first-block Fourier integrals. Its values uniquely specify the function. -/
def partialFourierSchwartz (Φ : SchwartzBruhat (Fin N → K)) :
    SchwartzBruhat (Fin N → K) :=
  Classical.choose (exists_partialFourierSchwartz ψ μ hsd e Φ)

@[simp]
theorem partialFourierSchwartz_join (Φ : SchwartzBruhat (Fin N → K))
    (ξ : Fin a → K) (v : Fin b → K) :
    partialFourierSchwartz ψ μ hsd e Φ (join e ξ v) =
      rowPartialFourierIntegral ψ μ e Φ ξ v :=
  Classical.choose_spec (exists_partialFourierSchwartz ψ μ hsd e Φ) ξ v

theorem partialFourierSchwartz_apply (Φ : SchwartzBruhat (Fin N → K)) (z : Fin N → K) :
    partialFourierSchwartz ψ μ hsd e Φ z =
      rowPartialFourierIntegral ψ μ e Φ (first e z) (second e z) := by
  simpa only [join_first_second] using
    partialFourierSchwartz_join ψ μ hsd e Φ (first e z) (second e z)

end Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

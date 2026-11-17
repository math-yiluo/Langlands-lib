import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAnalyticAssemblyStatement

/-! # Analyticity of the actual varying-dimensional atlas -/

universe u

open _root_.AlgebraicGeometry Set
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Analytic chart compatibility on each actual dimension piece passes to its
lifted charts on the original rational-point space. -/
theorem smoothSourceDimensionAnalyticAssembly :
    SmoothSourceDimensionAnalyticAssemblyStatement.{u} := by
  intro K _ hK σ hσ X hX hqs hls
  let := etaleChartTopology K X
  intro n e he e' he'
  let := etaleChartTopology K (SmoothDimensionPieces.space hX n)
  let := σ.chartedSpace n (SmoothDimensionPieces.space hX n)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls n)
  let := hσ n (SmoothDimensionPieces.space hX n)
    (SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls n)
  obtain ⟨c, hc, rfl⟩ := he
  obtain ⟨c', hc', rfl⟩ := he'
  rw [AnalyticPointStructure.liftDimensionChart_transition]
  have htrans := (contDiffGroupoid ω 𝓘(K, Fin n → K)).compatible hc hc'
  simpa only [contDiffPregroupoid, mfld_simps] using htrans.1

end Langlands.AlgebraicGeometry.AlgebraicSpace

import Langlands.Representation.RankinSelberg.AdjacentRankModelStarBase

/-! Final assembly of the fixed-character adjacent-rank model-star identity. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct GeneralLinear

universe uF uV

/-- The closed fixed-character adjacent-rank model-star identity, including
actual convergence of both scalar integrands. -/
theorem adjacentRankModelStar :
    AdjacentRankModelStarStatement.{uF,uV} := by
  intro p _ F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel _
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro ψ ν hself r V _ _ σ hσ ℓ χ Ψ g
  let : MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
  have : BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
  refine ⟨adjacentRankModelConvergence p F ψ ν hself r V σ hσ ℓ χ Ψ _, ?_, ?_⟩
  · exact adjacentRankTransformed_integrable_of_isSmooth F ψ ν hself r σ hσ.1.1 ℓ χ
      (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) (adjacentRankZeta F.Carrier r * g)
  · exact adjacentRankModelStar_equality_of_base F ψ ν hself σ ℓ χ
      (adjacentRankModelStar_base F ψ ν hself σ hσ.1.1 ℓ χ) Ψ g

end Langlands.RankinSelberg

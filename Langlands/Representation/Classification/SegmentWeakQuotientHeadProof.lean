import Langlands.Representation.Classification.SegmentWeakQuotientHeadStatement

/-! # Proof of the conditional weak segment quotient upgrade -/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

theorem segmentWeakQuotientHeadUpgrade :
    SegmentWeakQuotientHeadUpgrade.{uF, uV} F T := by
  intro hex
  let := T.topology
  intro Δ π
  constructor
  · rintro ⟨A, hA, hπ, q, hq⟩
    obtain ⟨σ, hσ, _⟩ := hex Δ
    obtain ⟨_, q₀, _, huniq⟩ := (T.isSegmentHead_iff Δ σ A hA).mp hσ
    refine ⟨A, hA, hπ, q, hq, ?_⟩
    intro W' _ _ π' hπ' q' hq'
    exact (huniq W' π' hπ' q' hq').trans
      (huniq _ π.representation hπ q hq).symm
  · exact fun h => h.isSegmentQuotient

end Langlands.Classification

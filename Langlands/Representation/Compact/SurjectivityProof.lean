import Langlands.Representation.Compact.SurjectivityStatement
import Langlands.Representation.Compact.ProjectionProof

namespace Langlands.Compact

universe uG uV uW

theorem fixedVectorSurjectivity : FixedVectorSurjectivity.{uG, uV, uW} := by
  intro G _ _ _ V _ _ W _ _ ρ σ hρ hσ K hK f hf w
  obtain ⟨v, hv⟩ := hf w.val
  refine ⟨⟨averageMap ρ hρ K hK v, averageMap_mem_fixedVectors ρ hρ K hK v⟩,
    Subtype.ext ?_⟩
  change f (averageMap ρ hρ K hK v) = w.val
  have hcomm := LinearMap.congr_fun (averageMap_commute ρ σ hρ hσ K hK f) v
  change f (averageMap ρ hρ K hK v) = averageMap σ hσ K hK (f v) at hcomm
  rw [hcomm, hv]
  exact averageMap_id σ hσ K hK w.val w.property

end Langlands.Compact

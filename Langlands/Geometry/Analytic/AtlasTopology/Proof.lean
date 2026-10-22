import Langlands.Geometry.Analytic.AtlasTopology.Statement
import Langlands.Geometry.Analytic.AtlasTopology.NetProperties

/-! # Quasinet topology and compact-net intersections -/

universe u v

namespace Langlands.Analytic.AtlasTopology

/-- The complete topology target, with no analytic or separation assumptions
beyond the exact hypotheses in each component. -/
theorem quasinetTopology : QuasinetTopologyStatement.{u, v} := by
  intro X _ Y _
  refine ⟨isNet_singleton_univ, ?_, ?_⟩
  · intro τ hτ
    refine ⟨hτ.covers, (fun _ h => hτ.mono h), hτ.isCoherentWith,
      hτ.isOpen_iff, hτ.isClosed_iff, hτ.continuous_iff,
      (fun _ h => hτ.product h), hτ.t2Space_iff,
      hτ.weaklyLocallyCompactSpace, ?_⟩
    intro hc hX
    let := hX
    exact hτ.locallyCompactSpace hc
  · intro τ hτ hc U hU V hV
    exact ⟨hτ.locallyCompactSpace_inter hc hU hV,
      hτ.isLocallyClosed_inter_left hc hU hV,
      hτ.isLocallyClosed_inter_right hc hU hV⟩

end Langlands.Analytic.AtlasTopology

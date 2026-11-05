import Langlands.Global.AdelicSpreadTopologicalPropertiesStatement
import Langlands.Global.AdelicFixedModelLocalCompactnessProof
import Langlands.Global.AdelicFixedModelSecondCountabilityProof
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Topological properties of actual adelic points from a specified spread -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.Global

/-- The actual spread point homeomorphisms transfer the fixed-model properties
to actual generic-fibre adelic points in precisely their spread topologies. -/
theorem adelicSpreadTopologicalProperties :
    AdelicSpreadTopologicalPropertiesStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S X _ _ Y e
    let := curvePlaceFixedModelAdelePointTopology k F S X
    let := curvePlaceSpreadAdelePointTopology k F S X Y e
    have h := adelicFixedModelLocalCompactness.1 k F S X
    let := adelicFixedModelSecondCountability.1 k F S X
    have H := curvePlaceSpreadAdelePointHomeomorph k F S X Y e
    refine ⟨H.locallyCompactSpace_iff.mp h.1,
      H.symm.secondCountableTopology, ?_⟩
    intro hSep
    let := h.2
    exact H.symm.isEmbedding.t2Space
  · intro K _ _ S X _ _ Y e
    let := numberFieldFixedModelAdelePointTopology K S X
    let := numberFieldSpreadAdelePointTopology K S X Y e
    have h := adelicFixedModelLocalCompactness.2 K S X
    let := adelicFixedModelSecondCountability.2 K S X
    have H := numberFieldSpreadAdelePointHomeomorph K S X Y e
    refine ⟨H.locallyCompactSpace_iff.mp h.1,
      H.symm.secondCountableTopology, ?_⟩
    intro hSep
    let := h.2
    exact H.symm.isEmbedding.t2Space

end Langlands.Global

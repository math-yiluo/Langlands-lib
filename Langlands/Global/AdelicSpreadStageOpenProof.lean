import Langlands.Global.AdelicSpreadStageOpenStatement
import Langlands.Global.AdelicFixedModelColimitOpenProof
import Langlands.Global.AdelicSpreadTopologyIndependenceProof

/-! # Open arithmetic stages in actual field-scheme adelic points -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- The fixed-model open stage maps remain open in actual field points with
the topology of any independent finite-type spread. -/
theorem curvePlaceSpreadStageOpen : CurvePlaceSpreadStageOpenStatement.{u} := by
  intro k F _ _ _ _ _ _ _ S U M N _ _ _ _ Y e f T
  dsimp only
  rw [← adelicSpreadTopologyIndependence.1 k F S U M N Y e f]
  let := curvePlaceFixedModelStageTopology k F S M T
  let := curvePlaceFixedModelAdelePointTopology k F S M
  let := curvePlaceSpreadAdelePointTopology k F S M Y e
  let h := curvePlaceSpreadAdelePointHomeomorph k F S M Y e
  have ho := adelicFixedModelColimitOpen.1 k F S M
  refine ⟨h.continuous.comp (ho.1 T).1, h.isOpenMap.comp (ho.1 T).2, ?_⟩
  intro _
  exact h.isOpenEmbedding.comp (ho.2.2 T)

/-- The same comparison for full number-field adeles retains every infinite
factor and requires separation only for the embedding assertion. -/
theorem numberFieldSpreadStageOpen : NumberFieldSpreadStageOpenStatement.{u} := by
  intro K _ _ S U M N _ _ _ _ Y e f T
  dsimp only
  rw [← adelicSpreadTopologyIndependence.2 K S U M N Y e f]
  let := numberFieldFixedModelStageTopology K S M T
  let := numberFieldFixedModelAdelePointTopology K S M
  let := numberFieldSpreadAdelePointTopology K S M Y e
  let h := numberFieldSpreadAdelePointHomeomorph K S M Y e
  have ho := adelicFixedModelColimitOpen.2 K S M
  refine ⟨h.continuous.comp (ho.1 T).1, h.isOpenMap.comp (ho.1 T).2, ?_⟩
  intro _
  exact h.isOpenEmbedding.comp (ho.2.2 T)

/-- Both arithmetic forms of openness of the actual stage-to-field-point map. -/
theorem adelicSpreadStageOpen : AdelicSpreadStageOpenStatement.{u} :=
  ⟨curvePlaceSpreadStageOpen, numberFieldSpreadStageOpen⟩

end Langlands.Global

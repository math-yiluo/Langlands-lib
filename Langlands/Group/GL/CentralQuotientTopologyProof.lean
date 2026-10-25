import Langlands.Group.GL.CentralQuotientTopologyStatement
import Langlands.Group.GL.CountabilityProof

/-! # Topology and Haar measures of actual central quotients -/

namespace Langlands

universe uG uF

private theorem centralQuotientHaarTopology (G : Type uG) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    CentralQuotientHaarTopology G := by
  have : IsClosed (Subgroup.center G : Set G) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set G))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro _ _
  constructor
  · exact ⟨MeasureTheory.Measure.haarMeasure (Classical.arbitrary _), inferInstance⟩
  · intro μ _
    infer_instance

/-- The full central quotients of actual p-adic general linear groups and their
product Levis have the topology and Haar properties needed for analytic comparison. -/
theorem glBlockCentralQuotientTopology : GLBlockCentralQuotientTopologyStatement.{uF} := by
  intro p _ F T
  let := T.topology
  intro n
  constructor
  · let := T.generalLinearTopologicalGroup n
    let := T.generalLinearT2Space n
    let := T.generalLinearLocallyCompactSpace n
    let := T.generalLinearSecondCountableTopology n
    exact centralQuotientHaarTopology (GeneralLinear n F.Carrier)
  · intro B
    let := T.leviTopology B
    let := T.leviTopologicalGroup B
    let := T.leviT2Space B
    let := T.leviLocallyCompactSpace B
    have : ∀ i : Fin B.length, SecondCountableTopology (GeneralLinear (B.size i) F.Carrier) :=
      fun i => T.generalLinearSecondCountableTopology (B.size i)
    exact centralQuotientHaarTopology (B.Levi F.Carrier)

end Langlands

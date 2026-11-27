import Langlands.AllFieldBZ.Group.GL.CentralQuotientTopologyStatement
import Langlands.AllFieldBZ.Group.GL.CountabilityProof
import Langlands.AllFieldBZ.Representation.Smooth.SmallRealizationProof
import Langlands.Group.GL.CentralQuotientTopologyProof

/-!
# All-field port of `Langlands.Group.GL.CentralQuotientTopologyProof`

The declarations of the original module that depend on the field are restated and
reproved over an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`); its field-independent declarations
are used unchanged. See the paired Markdown.
-/

namespace Langlands.AllFieldBZ

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

/-- The full central quotients of actual general linear groups over a local field and their
product Levis have the topology and Haar properties needed for analytic comparison. -/
theorem glBlockCentralQuotientTopology : GLBlockCentralQuotientTopologyStatement.{uF} := by
  intro F T
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

end Langlands.AllFieldBZ

import Langlands.Representation.Geometric.ConditionalAssembly
import Langlands.Representation.Geometric.CosetOrbitOrdering
import Langlands.Topology.GroupAction.FiniteOrbitProof
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Geometric.PadicParabolicBruhatProof
import Langlands.Representation.Geometric.ParabolicSupportGradedProof

/-! The normalized geometric lemma for actual p-adic general linear groups. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear

universe uF uV

/-- The actual normalized induction-Jacquet composite has the natural filtration
and standard-intersection geometric pieces in the published statement. -/
theorem padicGeometricLemma : PadicGeometricLemmaTheorem.{uF, uV} := by
  intro p _ F T n hn B C
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearT2Space n
  let := T.generalLinearSigmaCompactSpace n
  have hBruhat := padicParabolicBruhat.{uF} p F n hn B C
  have hfinite : Finite (DoubleCoset.Quotient
      (B.parabolic F.Carrier : Set (GeneralLinear n F.Carrier))
      (C.parabolic F.Carrier : Set (GeneralLinear n F.Carrier))) :=
    Finite.of_surjective _ hBruhat.surjective
  obtain ⟨m, ⟨s⟩⟩ :=
    (closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
      Langlands.Topology.finiteOrbitOrdering) (GeneralLinear n F.Carrier)
        (B.parabolic F.Carrier) (C.parabolic F.Carrier)
        (B.isClosed_parabolic F.Carrier) (C.isClosed_parabolic F.Carrier) hfinite
  choose S hS using fun w =>
    (padicStandardIntersectionsTheorem.{uF} p F n hn B C w).1
  choose R hR using fun w =>
    (padicStandardIntersectionsTheorem.{uF} p F n hn B C w).2
  apply geometricLemma_of_orderedCosets.{uF, uV} T B C s hBruhat S R hS hR
  intro e t ht
  exact padicParabolicSupportGradedTheorem.{uF, uV}
    p F T n hn B C m e t ht S R hS hR

end Langlands.Geometric

import Langlands.Representation.Geometric.ProductLeviGeometricLemmaStatement
import Langlands.Representation.Geometric.ProductLeviTailOrdering
import Langlands.Representation.Geometric.CosetOrbitOrdering
import Langlands.Topology.GroupAction.FiniteOrbitProof
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Geometric.PadicParabolicBruhatProof
import Langlands.Representation.Geometric.ParabolicSupportGradedProof

/-! The normalized geometric lemma inside an actual standard product Levi. -/

noncomputable section
namespace Langlands.Geometric
open GeneralLinear
universe uF uV

/-- The normalized product-Levi composite has the natural filtration and all
standard-intersection geometric pieces required by the published statement. -/
theorem padicProductLeviGeometricLemma : PadicProductLeviGeometricLemmaTheorem.{uF, uV} := by
  intro p _ F T n hn B Q S
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearNonarchimedean n
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearT2Space n
  let := T.generalLinearSigmaCompactSpace n
  let D := B.flatten Q
  let C := B.flatten S
  have hBruhat := padicParabolicBruhat.{uF} p F n hn D C
  have hfinite : Finite (DoubleCoset.Quotient
      (D.parabolic F.Carrier : Set (GeneralLinear n F.Carrier))
      (C.parabolic F.Carrier : Set (GeneralLinear n F.Carrier))) :=
    Finite.of_surjective _ hBruhat.surjective
  obtain ⟨m, ⟨s⟩⟩ :=
    (closedSubgroupOrbitOrdering_of_finiteOrbitOrdering
      Langlands.Topology.finiteOrbitOrdering) (GeneralLinear n F.Carrier)
        (D.parabolic F.Carrier) (C.parabolic F.Carrier)
        (D.isClosed_parabolic F.Carrier) (C.isClosed_parabolic F.Carrier) hfinite
  obtain ⟨a, b, _, t, _, hcut⟩ := exists_productLeviSupportCut T B Q S s
  let o := minimalPermutationOrdering D C t hBruhat
  let e := o.1
  let u := o.2.val
  have hrep : ∀ i, u.representative i = permutation n F.Carrier (e i).val :=
    o.2.property
  have hcut' : u.initialOrbits ⟨a, by omega⟩ =
      (coarseParabolicLocus (F := F) B Q)ᶜ :=
    (minimalPermutationOrdering_initialOrbits D C t hBruhat ⟨a, by omega⟩).trans hcut
  have he := blockWeyl_iff_tailIndex T B Q S e u hrep hcut'
  let eTail := blockTailEquiv B Q S e he
  choose U hU using fun w =>
    (padicStandardIntersectionsTheorem.{uF} p F n hn D C w).1
  choose V hV using fun w =>
    (padicStandardIntersectionsTheorem.{uF} p F n hn D C w).2
  have hgraded := padicParabolicSupportGradedTheorem.{uF, uV}
    p F T n hn D C (a + b) e u hrep U V hU hV
  have hker := productLeviSupportCut_ker.{uF, uV} T B Q S u hcut'
  have hsurj := productLeviQuotientMap_surjective.{uF, uV} T B Q S
  let filtration := parabolicJacquetSupportFiltration.{uF, uV} T D C u
  let α := productLeviQuotientMap.{uF, uV} T B Q S
  refine ⟨(fun w => U w.val), (fun w => V w.val),
    (fun w => hU w.val), (fun w => hV w.val), b, eTail, Equiv.refl _, ?_⟩
  refine ⟨filtration.quotientTail α hker hsurj, ?_⟩
  have htail := hgraded.quotientTail α hker hsurj
  intro i
  simpa only [Function.comp_apply, Equiv.refl_apply, eTail, blockTailEquiv_val] using htail i

end Langlands.Geometric

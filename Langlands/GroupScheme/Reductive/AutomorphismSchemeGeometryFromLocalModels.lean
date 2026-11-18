import Langlands.GroupScheme.Reductive.AutomorphismSchemeGeometryStatement
import Langlands.GroupScheme.Reductive.AutomorphismOuterGeometryOfPinnedCharts
import Langlands.GroupScheme.Adjoint.ReductiveRelativeExistenceStatement
import Langlands.GroupScheme.IsomorphismSchemeOpenDescent
import Langlands.GroupScheme.IsomorphismSchemeSingleCoverDescent

/-! # Global automorphism geometry from pinned local representatives -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- The full general-base geometry follows from pinned full Aut representatives,
pinned orbit classification, and independently proved relative adjoint existence. -/
theorem reductiveAutomorphismSchemeGeometry_of_pinnedLocalRepresentatives
    (hchart : PinnedOuterIsomorphismChartStatement.{u})
    (hAdj : RelativeAdjointQuotientExistenceStatement.{u})
    (hlocal : ∀ M : AffinePinnedModel.{u},
      ∃ I : GroupIsomorphismScheme M.group M.group,
        Smooth I.parameter.hom ∧ IsSeparated I.parameter.hom) :
    ReductiveAutomorphismSchemeGeometryStatement.{u} := by
  intro S G hG
  let C := AffinePinnedAtlas.ofReductive hG
  let modelI (i : S) := Classical.choose (hlocal (C.chart i).model)
  have modelSm (i : S) : Smooth (modelI i).parameter.hom :=
    (Classical.choose_spec (hlocal (C.chart i).model)).1
  have modelSep (i : S) : IsSeparated (modelI i).parameter.hom :=
    (Classical.choose_spec (hlocal (C.chart i).model)).2
  let L (i : C.cover.I₀) : GroupIsomorphismScheme
      ((GroupScheme.baseChange (C.cover.f i)).obj G)
      ((GroupScheme.baseChange (C.cover.f i)).obj G) :=
    ((modelI i).precompose (C.chart i).iso).postcompose (C.chart i).iso.symm
  have Lsm (i : C.cover.I₀) : Smooth (L i).parameter.hom := modelSm i
  have Lsep (i : C.cover.I₀) : IsSeparated (L i).parameter.hom := modelSep i
  let V := sigmaOpenCover (fun i : S => (C.chart i).model.base)
  let E (i : V.I₀) :
      (GroupScheme.baseChange (V.f i)).obj ((GroupScheme.baseChange C.projection).obj G) ≅
        (GroupScheme.baseChange (C.cover.f i)).obj G :=
    Descent.pullbackComparison C.projection (V.f i) (C.cover.f i)
      (Sigma.ι_comp_desc (fun i : S => (C.chart i).map) i) G
  let Jloc (i : V.I₀) : GroupIsomorphismScheme
      ((GroupScheme.baseChange (V.f i)).obj ((GroupScheme.baseChange C.projection).obj G))
      ((GroupScheme.baseChange (V.f i)).obj ((GroupScheme.baseChange C.projection).obj G)) :=
    ((L i).precompose (E i)).postcompose (E i).symm
  let J := GroupIsomorphismScheme.ofOpenCover V Jloc
  let : Smooth J.parameter.hom :=
    J.property_of_openCover (@Smooth.{u}) V Jloc (fun i => Lsm i)
  have hGU : IsReductive ((GroupScheme.baseChange C.projection).obj G) :=
    hG.baseChange C.projection
  obtain ⟨A, q, hq⟩ :=
    (ReductiveRelativeAdjointQuotientExistenceStatement.of_affine hAdj) S G hG
  let qU := (GroupScheme.baseChange C.projection).map q
  let hqU := hq.baseChange C.projection
  obtain ⟨OU, hOUe, hOUs, hOUa, _, _⟩ :=
    exists_automorphismOuterGeometry_of_pinnedCharts hchart hGU qU hqU J
  let O : OuterIsomorphismScheme J (hq.innerAction.baseChange C.projection) :=
    { parameter := OU.parameter
      classMap := OU.classMap
      flat := OU.flat
      surjective := OU.surjective
      quasiCompact := OU.quasiCompact
      invariant := by simpa only [hq.innerAction_baseChange] using OU.invariant
      orbit := by simpa only [hq.innerAction_baseChange] using OU.orbit }
  let : Etale O.parameter.hom := hOUe
  let : IsSeparated O.parameter.hom := hOUs
  let : IsAffineHom O.classMap.left := hOUa
  have ha : hq.innerAction.IsFaithful :=
    AutomorphicAction.isFaithful_of_isFppfQuotient_center hq.isQuotient
      hq.innerAction hq.innerAction_restrict
  let I := GroupIsomorphismScheme.ofSingleLocalOuterQuotient
    C.projection hq.innerAction ha J O
  refine ⟨I, I.property_of_etaleCover (@Smooth.{u}) C.cover L Lsm,
    I.property_of_etaleCover (@IsSeparated.{u}) C.cover L Lsep, ?_⟩
  intro A q hq
  exact exists_automorphismOuterGeometry_of_pinnedCharts hchart hG q hq I

/-- Select the actual global full Aut representative produced by the
pinned-local construction and affine outer-quotient descent. -/
def automorphismSchemeOfPinnedLocalRepresentatives
    (hchart : PinnedOuterIsomorphismChartStatement.{u})
    (hAdj : RelativeAdjointQuotientExistenceStatement.{u})
    (hlocal : ∀ M : AffinePinnedModel.{u},
      ∃ I : GroupIsomorphismScheme M.group M.group,
        Smooth I.parameter.hom ∧ IsSeparated I.parameter.hom)
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G) :
    GroupIsomorphismScheme G G :=
  Classical.choose
    (reductiveAutomorphismSchemeGeometry_of_pinnedLocalRepresentatives hchart hAdj hlocal S G hG)

end Langlands.GroupScheme

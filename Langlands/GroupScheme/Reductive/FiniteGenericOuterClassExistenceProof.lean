import Langlands.GroupScheme.Reductive.FiniteGenericOuterClassExistenceStatement
import Langlands.GroupScheme.Reductive.OuterIsomorphismFromPinnedCharts
import Langlands.GroupScheme.Reductive.PinnedOuterIsomorphismChartProof
import Langlands.GroupScheme.OuterIsomorphismParameterGeometry
import Langlands.GroupScheme.OuterClassEtaleCover

/-! # A finite carrier for every prescribed generic outer class -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supplied outer quotient carries the prescribed generic class on a finite scheme. -/
theorem finiteGenericOuterClassExistence :
    FiniteGenericOuterClassExistenceStatement.{u} := by
  intro R _ _ _ K _ _ _ G H hG hH f A q hq I O
  let atlasG := AffinePinnedAtlas.ofReductive hG
  let atlasH := AffinePinnedAtlas.ofReductive hH
  let cover := Precoverage.ZeroHypercover.inter (J := Scheme.precoverage @Etale)
    atlasG.cover atlasH.cover
  let : Smooth A.X.hom := hq.isReductive_target.smooth
  obtain ⟨_, hSeparated, hTrivializations⟩ := O.geometry_of_localConstants cover (by
    rintro ⟨i, j⟩
    let b := cover.f (i, j)
    let g := pullback.fst (atlasG.cover.f i) (atlasH.cover.f j)
    let h := pullback.snd (atlasG.cover.f i) (atlasH.cover.f j)
    let chartG := atlasG.chart i
    let chartH := atlasH.chart j
    let isoG : (baseChange b).obj G ≅ chartG.model.groupOver g :=
      (Descent.pullbackComparison chartG.map g b rfl G).symm ≪≫
        (baseChange g).mapIso chartG.iso
    let isoH : (baseChange b).obj H ≅ chartH.model.groupOver h :=
      (Descent.pullbackComparison chartH.map h b pullback.condition.symm H).symm ≪≫
        (baseChange h).mapIso chartH.iso
    obtain ⟨D, sectionMap, hSection⟩ :=
      pinnedOuterIsomorphismChart.constantSection_of_isomorphisms
        chartG.model chartH.model g h isoG isoH ((baseChange b).map q)
        (hq.baseChange b) (I.baseChange b)
    have hAction : ∀ (T : Over (cover.X (i, j))), Function.Bijective
        (fun z : (T ⟶ ((baseChange b).obj A).X) ×
            (T ⟶ GroupIsomorphismScheme.constantParameter (cover.X (i, j)) D) =>
          lift z.1 (z.2 ≫ sectionMap) ≫ (I.baseChange b).actionHom
            (hq.innerAction.baseChange b)) := by
      rw [hq.innerAction_baseChange]
      exact hSection
    exact ⟨D, I.localSection b sectionMap,
      I.localSection_bijective hq.innerAction b sectionMap hAction⟩)
  let : IsSeparated O.parameter.hom := hSeparated
  exact ⟨FiniteGenericOuterClass.ofEtaleCover R K O cover hTrivializations
    (I.classify (LocalGroupIso.ofBaseChangeIso (U := Over.mk (Spec.algebraMap R K)) f))⟩

end Langlands.GroupScheme

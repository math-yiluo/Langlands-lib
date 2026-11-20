import Langlands.Geometry.Analytic.InducedSiteEssSurj
import Langlands.Geometry.Analytic.InducedSiteBaseIso
import Langlands.Geometry.Analytic.InducedSiteFull
import Langlands.Geometry.Analytic.InducedSiteCoverings
import Langlands.Geometry.Analytic.InducedSiteEquivalenceStatement

/-! # Induction on equivariant quasi-étale sites is an equivalence

Assembly of Berkovich's Example 1.2.1(i) (quasi-étale case) from two statements taken as
hypotheses: `OpenPartitionCoproductStatement` and `QuasiEtaleOpenRestrictionStatement`. -/

noncomputable section

universe u v z

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  (hP : OpenPartitionCoproductStatement.{u, v, z})
  (hR : QuasiEtaleOpenRestrictionStatement.{u, max z v})
  (hH : IsOpen (H : Set G)) (hC : ContinuityStatement.{u, v, z})
  (hQ : MorphismPropertyStatement.{u, v, z}) (X : GSpace.{u, max z v, max z v} K H)

include hP hR in
/-- Induction `Qét(X(H)) ⥤ Qét(X_{G/H}(G))` is essentially surjective. -/
theorem essSurj_quasiEtaleSiteInduction : (quasiEtaleSiteInduction hH hC hQ X).EssSurj :=
  essSurj_quasiEtaleSiteInduction_of_isIso hH hC hQ hP hR fun π => isIso_lift_baseInclusion π hP

include hP hR in
/-- Induction `Qét(X(H)) ⥤ Qét(X_{G/H}(G))` is an equivalence of categories. -/
theorem isEquivalence_quasiEtaleSiteInduction :
    (quasiEtaleSiteInduction hH hC hQ X).IsEquivalence where
  full := full_quasiEtaleSiteInduction hP hH hC hQ X
  essSurj := essSurj_quasiEtaleSiteInduction hP hR hH hC hQ X

/-- Berkovich's Example 1.2.1(i), quasi-étale case, from `OpenPartitionCoproductStatement` and
`QuasiEtaleOpenRestrictionStatement`. -/
theorem quasiEtaleSiteEquivalenceStatement_of
    (hP : OpenPartitionCoproductStatement.{u, v, z})
    (hR : QuasiEtaleOpenRestrictionStatement.{u, max z v}) :
    QuasiEtaleSiteEquivalenceStatement.{u, v, z} := by
  intro K _ _ _ G _ _ _ H hH hC hQ X
  exact ⟨isEquivalence_quasiEtaleSiteInduction hP hR hH hC hQ X,
    fun U R => map_quasiEtaleSiteInduction_mem_iff hH hC hQ X U R⟩

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

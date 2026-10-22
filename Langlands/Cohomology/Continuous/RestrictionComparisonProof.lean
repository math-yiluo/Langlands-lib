import Langlands.Cohomology.Continuous.RestrictionComparisonStatement

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

set_option backward.isDefEq.respectTransparency false in
theorem finiteRestrictionCochains_comp_stage (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G) :
    finiteRestrictionCochains A H N ≫
        finiteStageCochainMap (A.restrict H.toSubgroup) (restrictOpenNormal H N) =
      finiteStageCochainMap A N ≫ continuousRestrictionCochains A H.toSubgroup := by
  apply (cancel_mono
    (continuousToOrdinaryCochains (A.restrict H.toSubgroup).toTopRep)).mp
  rw [Category.assoc, finiteStageCochainMap_comp_comparison]
  unfold continuousRestrictionCochains
  rw [Category.assoc, continuousToOrdinaryCochains_naturality,
    ← Category.assoc, finiteStageCochainMap_comp_comparison]
  unfold finiteRestrictionCochains ordinaryInflationCochains
  rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
  apply groupCohomology.cochainsMap_congr
  · ext g
    rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Finite ordinary restriction commutes with the actual continuous restriction map. -/
theorem finiteRestriction_comp_stage (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G) (q : ℕ) :
    finiteRestriction A H N q ≫
        finiteStageToContinuous (A.restrict H.toSubgroup) (restrictOpenNormal H N) q =
      finiteStageToContinuous A N q ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (continuousRestriction A H.toSubgroup q) := by
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} k) (ComplexShape.up ℕ) q).map
      (ContinuousCohomology.cochainsMap (subgroupInclusion H.toSubgroup)
        (𝟙 (A.restrict H.toSubgroup).toTopRep)))
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  change HomologicalComplex.homologyMap (continuousRestrictionCochains A H.toSubgroup) q ≫
      (((TopRep.homogeneousCochains (A.restrict H.toSubgroup).toTopRep).sc q).mapHomologyIso
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom =
    (((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom ≫
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (continuousRestriction A H.toSubgroup q) at h
  unfold finiteRestriction finiteStageToContinuous
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    finiteRestrictionCochains_comp_stage, HomologicalComplex.homologyMap_comp,
    Category.assoc, h, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The colimit restriction comparison uses exactly the existing continuous restriction. -/
theorem finiteQuotientRestriction_comp_comparison (A : DiscreteModule k G)
    (H : OpenSubgroup G) (q : ℕ) :
    finiteQuotientRestriction A H q ≫
        finiteQuotientComparison (A.restrict H.toSubgroup) q =
      finiteQuotientComparison A q ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (continuousRestriction A H.toSubgroup q) := by
  apply Limits.colimit.hom_ext
  intro N
  unfold finiteQuotientRestriction
  rw [← Category.assoc, Limits.colimit.ι_desc]
  change (finiteRestriction A H (OrderDual.ofDual N) q ≫
      finiteStageToColimit (A.restrict H.toSubgroup).toRep
        (restrictOpenNormal H (OrderDual.ofDual N)) q) ≫ _ =
      finiteStageToColimit A.toRep (OrderDual.ofDual N) q ≫ _
  rw [Category.assoc, finiteStageToColimit_comp_comparison, finiteRestriction_comp_stage,
    ← Category.assoc, finiteStageToColimit_comp_comparison]

/-- Restriction commutes with the comparison in cochains and every cohomology degree. -/
theorem restrictionComparisonLaws : RestrictionComparisonLaws.{u} := by
  intro k G _ _ _ _ _ A H
  exact ⟨fun N => finiteRestrictionCochains_comp_stage A H N,
    fun N q => finiteRestriction_comp_stage A H N q,
    fun q => finiteQuotientRestriction_comp_comparison A H q⟩

end Langlands.Continuous

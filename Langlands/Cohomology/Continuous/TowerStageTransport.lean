import Langlands.Cohomology.Continuous.TowerTransport
import Langlands.Cohomology.Continuous.RestrictionMaps

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [Group G]

/-- The quotient map induced by identifying a subgroup with its nested coordinates. -/
def towerQuotientHom {K H : Subgroup G} (h : K ≤ H) (N : Subgroup G) [N.Normal] :
    K.subgroupOf H ⧸ (N.comap H.subtype).comap (K.subgroupOf H).subtype →*
      K ⧸ N.comap K.subtype :=
  QuotientGroup.map _ _ (Subgroup.subgroupOfEquivOfLe h).toMonoidHom (fun _ hx => hx)

/-- Fixed coefficients retain their values under the subgroup tower coordinate map. -/
noncomputable def towerFixedCoefficient (A : Rep.{u} k G)
    {K H : Subgroup G} (h : K ≤ H) (N : Subgroup G) [N.Normal] :
    Rep.res (towerQuotientHom h N) ((Rep.res K.subtype A).quotientToInvariants
      (N.comap K.subtype)) ⟶
    (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype A)).quotientToInvariants
      ((N.comap H.subtype).comap (K.subgroupOf H).subtype) :=
  Rep.ofHom
    { toLinearMap :=
        { toFun x := ⟨x.1, fun n => x.2 ⟨⟨n.1.1.1, n.1.2⟩, n.2⟩⟩
          map_add' _ _ := Subtype.ext rfl
          map_smul' _ _ := Subtype.ext rfl }
      isIntertwining' q := by
        refine QuotientGroup.induction_on q (fun g => ?_)
        ext x
        rfl }

variable [TopologicalSpace k] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual finite cochain map from direct to nested subgroup coordinates. -/
noncomputable def finiteTowerCochains (A : DiscreteModule k G)
    {K H : OpenSubgroup G} (h : K.toSubgroup ≤ H.toSubgroup)
    (N : OpenNormalSubgroup G) :
    groupCohomology.inhomogeneousCochains
        (finiteQuotientRep (A.restrict K.toSubgroup).toRep (restrictOpenNormal K N)) ⟶
      groupCohomology.inhomogeneousCochains
        (finiteQuotientRep
          ((A.restrict H.toSubgroup).restrict (towerOpenSubgroup K H).toSubgroup).toRep
          (restrictOpenNormal (towerOpenSubgroup K H) (restrictOpenNormal H N))) :=
  groupCohomology.cochainsMap (towerQuotientHom h N.toSubgroup)
    (towerFixedCoefficient A.toRep h N.toSubgroup)

/-- The underlying continuous cochain map for the same tower coordinates. -/
noncomputable def continuousTowerCochains (A : DiscreteModule k G)
    {K H : Subgroup G} (h : K ≤ H) :
    underlyingContinuousCochains (A.restrict K).toTopRep ⟶
      underlyingContinuousCochains ((A.restrict H).restrict (K.subgroupOf H)).toTopRep :=
  ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (ContinuousCohomology.cochainsMap
        (Subgroup.subgroupOfContinuousMulEquivOfLe h : K.subgroupOf H →ₜ* K)
        (continuousTowerCoefficientIso A h).hom)

set_option backward.isDefEq.respectTransparency false in
theorem finiteTowerCochains_comp_stage (A : DiscreteModule k G)
    {K H : OpenSubgroup G} (h : K.toSubgroup ≤ H.toSubgroup)
    (N : OpenNormalSubgroup G) :
    finiteTowerCochains A h N ≫
        finiteStageCochainMap
          ((A.restrict H.toSubgroup).restrict (towerOpenSubgroup K H).toSubgroup)
          (restrictOpenNormal (towerOpenSubgroup K H) (restrictOpenNormal H N)) =
      finiteStageCochainMap (A.restrict K.toSubgroup) (restrictOpenNormal K N) ≫
        continuousTowerCochains A h := by
  apply (cancel_mono (continuousToOrdinaryCochains
    ((A.restrict H.toSubgroup).restrict (towerOpenSubgroup K H).toSubgroup).toTopRep)).mp
  rw [Category.assoc, finiteStageCochainMap_comp_comparison]
  have hc : continuousTowerCochains A h ≫ continuousToOrdinaryCochains
        ((A.restrict H.toSubgroup).restrict (towerOpenSubgroup K H).toSubgroup).toTopRep =
      continuousToOrdinaryCochains (A.restrict K.toSubgroup).toTopRep ≫
        groupCohomology.cochainsMap (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
          (Rep.ofHom (continuousTowerCoefficientIso A h).hom.hom.toIntertwiningMap) :=
    continuousToOrdinaryCochains_naturality _ _
      (Subgroup.subgroupOfContinuousMulEquivOfLe h :
        K.toSubgroup.subgroupOf H.toSubgroup →ₜ* K.toSubgroup)
      (continuousTowerCoefficientIso A h).hom
  rw [Category.assoc, hc, ← Category.assoc, finiteStageCochainMap_comp_comparison]
  unfold finiteTowerCochains ordinaryInflationCochains
  rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
  apply groupCohomology.cochainsMap_congr
  · ext g
    rfl
  · rfl

/-- The induced map on genuine finite-quotient cohomology in every natural degree. -/
noncomputable def finiteTowerCohomology (A : DiscreteModule k G)
    {K H : OpenSubgroup G} (h : K.toSubgroup ≤ H.toSubgroup)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    groupCohomology
        (finiteQuotientRep (A.restrict K.toSubgroup).toRep (restrictOpenNormal K N)) q ⟶
      groupCohomology
        (finiteQuotientRep
          ((A.restrict H.toSubgroup).restrict (towerOpenSubgroup K H).toSubgroup).toRep
          (restrictOpenNormal (towerOpenSubgroup K H) (restrictOpenNormal H N))) q :=
  HomologicalComplex.homologyMap (finiteTowerCochains A h N) q

set_option backward.isDefEq.respectTransparency false in
/-- Finite-stage inflation commutes with the genuine continuous tower isomorphism. -/
theorem finiteTowerCohomology_comp_stage (A : DiscreteModule k G)
    {K H : OpenSubgroup G} (h : K.toSubgroup ≤ H.toSubgroup)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    finiteTowerCohomology A h N q ≫
        finiteStageToContinuous
          ((A.restrict H.toSubgroup).restrict (towerOpenSubgroup K H).toSubgroup)
          (restrictOpenNormal (towerOpenSubgroup K H) (restrictOpenNormal H N)) q =
      finiteStageToContinuous (A.restrict K.toSubgroup) (restrictOpenNormal K N) q ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (continuousTowerCohomologyIso A h q).hom := by
  have ht := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} k) (ComplexShape.up ℕ) q).map
      (ContinuousCohomology.cochainsMap
        (Subgroup.subgroupOfContinuousMulEquivOfLe h :
          K.toSubgroup.subgroupOf H.toSubgroup →ₜ* K.toSubgroup)
        (continuousTowerCoefficientIso A h).hom))
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  change HomologicalComplex.homologyMap (continuousTowerCochains A h) q ≫
      (((TopRep.homogeneousCochains
        ((A.restrict H.toSubgroup).restrict (towerOpenSubgroup K H).toSubgroup).toTopRep).sc q).mapHomologyIso (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom =
    (((TopRep.homogeneousCochains (A.restrict K.toSubgroup).toTopRep).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom ≫
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (continuousTowerCohomologyIso A h q).hom at ht
  unfold finiteTowerCohomology finiteStageToContinuous
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    finiteTowerCochains_comp_stage, HomologicalComplex.homologyMap_comp,
    Category.assoc, ht, ← Category.assoc]

end Langlands.Continuous

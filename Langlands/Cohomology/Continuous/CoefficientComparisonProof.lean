import Langlands.Cohomology.Continuous.CoefficientComparisonStatement

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

set_option backward.isDefEq.respectTransparency false in
theorem finiteCochainCoefficient_comp_stage {A B : DiscreteModule k G}
    (f : A.toTopRep ⟶ B.toTopRep) (N : OpenNormalSubgroup G) :
    (finiteCochainCoefficient (Rep.ofHom f.hom.toIntertwiningMap)).app
        (OrderDual.toDual N) ≫ finiteStageCochainMap B N =
      finiteStageCochainMap A N ≫ continuousCoefficientCochains f := by
  apply (cancel_mono (continuousToOrdinaryCochains B.toTopRep)).mp
  rw [Category.assoc, finiteStageCochainMap_comp_comparison]
  unfold continuousCoefficientCochains
  rw [Category.assoc, continuousToOrdinaryCochains_naturality,
    ← Category.assoc, finiteStageCochainMap_comp_comparison]
  change groupCohomology.cochainsMap (MonoidHom.id _)
      ((Rep.quotientToInvariantsFunctor k N.toSubgroup).map
        (Rep.ofHom f.hom.toIntertwiningMap)) ≫ ordinaryInflationCochains B N =
    ordinaryInflationCochains A N ≫
      groupCohomology.cochainsMap (MonoidHom.id G) (Rep.ofHom f.hom.toIntertwiningMap)
  unfold ordinaryInflationCochains
  rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
  apply groupCohomology.cochainsMap_congr
  · ext x
    rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
theorem finiteCohomologyCoefficient_comp_stage {A B : DiscreteModule k G}
    (f : A.toTopRep ⟶ B.toTopRep) (N : OpenNormalSubgroup G) (q : ℕ) :
    (finiteCohomologyCoefficient (Rep.ofHom f.hom.toIntertwiningMap) q).app
        (OrderDual.toDual N) ≫ finiteStageToContinuous B N q =
      finiteStageToContinuous A N q ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q) := by
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} k) (ComplexShape.up ℕ) q).map
      (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f))
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  change HomologicalComplex.homologyMap (continuousCoefficientCochains f) q ≫
      (((TopRep.homogeneousCochains B.toTopRep).sc q).mapHomologyIso
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom =
    (((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom ≫
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q) at h
  change HomologicalComplex.homologyMap
    ((finiteCochainCoefficient (Rep.ofHom f.hom.toIntertwiningMap)).app (OrderDual.toDual N)) q ≫
      finiteStageToContinuous B N q = _
  unfold finiteStageToContinuous
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    finiteCochainCoefficient_comp_stage, HomologicalComplex.homologyMap_comp,
    Category.assoc, h, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The comparison is natural in genuine continuous coefficient morphisms. -/
theorem finiteQuotientComparison_coefficient_naturality {A B : DiscreteModule k G}
    (f : A.toTopRep ⟶ B.toTopRep) (q : ℕ) :
    finiteQuotientCoefficient (Rep.ofHom f.hom.toIntertwiningMap) q ≫
        finiteQuotientComparison B q =
      finiteQuotientComparison A q ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q) := by
  apply Limits.colimit.hom_ext
  intro N
  unfold finiteQuotientCoefficient
  rw [← Category.assoc, Limits.ι_colimMap, Category.assoc]
  change (finiteCohomologyCoefficient (Rep.ofHom f.hom.toIntertwiningMap) q).app N ≫
      (finiteStageToColimit B.toRep (OrderDual.ofDual N) q ≫ finiteQuotientComparison B q) =
    finiteStageToColimit A.toRep (OrderDual.ofDual N) q ≫ _
  rw [finiteStageToColimit_comp_comparison]
  calc
    _ = finiteStageToContinuous A (OrderDual.ofDual N) q ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (ContinuousCohomology.map (ContinuousMonoidHom.id G) f q) :=
      finiteCohomologyCoefficient_comp_stage f (OrderDual.ofDual N) q
    _ = _ := by rw [← Category.assoc, finiteStageToColimit_comp_comparison]

/-- Coefficient naturality holds on cochains, finite-stage cohomology, and the colimit. -/
theorem coefficientComparisonLaws : CoefficientComparisonLaws.{u} := by
  intro k G _ _ _ _ _ A B f
  exact ⟨fun N => finiteCochainCoefficient_comp_stage f N,
    fun N q => finiteCohomologyCoefficient_comp_stage f N q,
    fun q => finiteQuotientComparison_coefficient_naturality f q⟩

end Langlands.Continuous

import Langlands.Cohomology.Continuous.FiniteQuotientSystem
import Langlands.Cohomology.Continuous.CochainComparisonLawsProof
import Mathlib.Algebra.Homology.HomologicalComplexLimits

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] continuousToOrdinaryCochains_isIso continuousToOrdinary_isIso

/-- The underlying module complex of Mathlib's continuous homogeneous cochains. -/
abbrev underlyingContinuousCochains (A : TopRep.{u} k G) :=
  ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (TopRep.homogeneousCochains A)

theorem homogeneousComparison_f_injective (A : TopRep.{u} k G) (n : ℕ) :
    Function.Injective ((homogeneousComparison A).f n) := by
  intro f g h
  apply Subtype.ext
  apply nestedEval_injective A (n + 1)
  funext x
  change homogeneousTermMap A n f = homogeneousTermMap A n g at h
  have hx := congrArg (fun t : Rep.diagonal k G (n + 1) ⟶ Rep.of A.ρ.toRepresentation =>
    t.hom (MonoidAlgebra.single x 1)) h
  simpa only [homogeneousTermMap_single A, one_smul] using hx

theorem continuousToOrdinaryCochains_f_injective (A : TopRep.{u} k G) (n : ℕ) :
    Function.Injective ((continuousToOrdinaryCochains A).f n) := by
  apply Function.Injective.comp
    ((ModuleCat.mono_iff_injective ((standardToInhomogeneousIso A).hom.f n)).mp inferInstance)
    (homogeneousComparison_f_injective A n)

instance continuousToOrdinaryCochains_mono (A : TopRep.{u} k G) :
    Mono (continuousToOrdinaryCochains A) :=
  HomologicalComplex.mono_of_mono_f _ (fun n =>
    (ModuleCat.mono_iff_injective _).mpr (continuousToOrdinaryCochains_f_injective A n))

/-- The canonical ordinary-cochain map from a finite stage into ordinary cochains of G. -/
noncomputable def ordinaryInflationCochains (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) :
    groupCohomology.inhomogeneousCochains (finiteQuotientRep A.toRep N) ⟶
      groupCohomology.inhomogeneousCochains A.toRep :=
  groupCohomology.cochainsMap (QuotientGroup.mk' N.toSubgroup)
    (Rep.ofHom (A.toRep.ρ.quotientToInvariants_lift N.toSubgroup))

set_option backward.isDefEq.respectTransparency false in
/-- Actual ordinary finite-stage cochains map into the nested continuous complex. -/
noncomputable def finiteStageCochainMap (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) :
    groupCohomology.inhomogeneousCochains (finiteQuotientRep A.toRep N) ⟶
      underlyingContinuousCochains A.toTopRep := by
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
  have : IsIso (continuousToOrdinaryCochains (finiteQuotientTopRep A N)) :=
    continuousToOrdinaryCochains_isIso (finiteQuotientTopRep A N)
  exact inv (continuousToOrdinaryCochains (finiteQuotientTopRep A N)) ≫
    ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
      (ContinuousCohomology.cochainsMap (quotientProjection N) (fixedCoefficientInclusion A N))

set_option backward.isDefEq.respectTransparency false in
theorem finiteStageCochainMap_comp_comparison (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) :
    finiteStageCochainMap A N ≫ continuousToOrdinaryCochains A.toTopRep =
      ordinaryInflationCochains A N := by
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
  unfold finiteStageCochainMap
  rw [Category.assoc, continuousToOrdinaryCochains_naturality,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem comparison_comp_finiteStageCochainMap (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) :
    continuousToOrdinaryCochains (finiteQuotientTopRep A N) ≫ finiteStageCochainMap A N =
      ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
        (ContinuousCohomology.cochainsMap (quotientProjection N) (fixedCoefficientInclusion A N)) := by
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
  unfold finiteStageCochainMap
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem finiteStageCochainMap_refinement (A : DiscreteModule k G)
    {M N : OpenNormalSubgroup G} (h : M ≤ N) :
    groupCohomology.cochainsMap (quotientTransition h) (fixedTransition A.toRep h) ≫
      finiteStageCochainMap A M = finiteStageCochainMap A N := by
  apply (cancel_mono (continuousToOrdinaryCochains A.toTopRep)).mp
  rw [Category.assoc, finiteStageCochainMap_comp_comparison,
    finiteStageCochainMap_comp_comparison]
  unfold ordinaryInflationCochains
  rw [← groupCohomology.cochainsMap_comp]
  apply groupCohomology.cochainsMap_congr
  · ext g
    rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite quotient complex diagram has its canonical continuous cocone. -/
noncomputable def finiteStageCochainCocone (A : DiscreteModule k G) :
    Limits.Cocone (finiteQuotientCochainDiagram A.toRep) where
  pt := underlyingContinuousCochains A.toTopRep
  ι :=
    { app := fun N => finiteStageCochainMap A (OrderDual.ofDual N)
      naturality := fun N M f => by
        dsimp only [finiteQuotientCochainDiagram]
        simp only [Functor.const_obj_map]
        exact finiteStageCochainMap_refinement A
          (M := OrderDual.ofDual M) (N := OrderDual.ofDual N)
          (leOfHom (X := FiniteQuotientIndex (G := G)) f) }

/-- The homology cocone of the actual finite-stage cochain maps. -/
noncomputable def finiteStageHomologyCocone (A : DiscreteModule k G) (q : ℕ) :
    Limits.Cocone (finiteQuotientDiagram A.toRep q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) q).mapCocone
    (finiteStageCochainCocone A)

/-- The actual comparison from the directed ordinary cohomology system to continuous cohomology. -/
noncomputable def finiteQuotientComparison (A : DiscreteModule k G) (q : ℕ) :
    finiteQuotientCohomology A.toRep q ⟶
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology q A.toTopRep) :=
  Limits.colimit.desc (finiteQuotientDiagram A.toRep q) (finiteStageHomologyCocone A q) ≫
    (((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom

/-- A finite ordinary cohomology class maps to actual continuous cohomology. -/
noncomputable def finiteStageToContinuous (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    groupCohomology (finiteQuotientRep A.toRep N) q ⟶
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).obj (continuousCohomology q A.toTopRep) :=
  HomologicalComplex.homologyMap (finiteStageCochainMap A N) q ≫
    (((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).hom

set_option backward.isDefEq.respectTransparency false in
theorem finiteStageToColimit_comp_comparison (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    finiteStageToColimit A.toRep N q ≫ finiteQuotientComparison A q =
      finiteStageToContinuous A N q := by
  unfold finiteStageToColimit finiteQuotientComparison
  rw [← Category.assoc, Limits.colimit.ι_desc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem finiteStageToContinuous_refinement (A : DiscreteModule k G)
    {M N : OpenNormalSubgroup G} (h : M ≤ N) (q : ℕ) :
    finiteInflation A.toRep q h ≫ finiteStageToContinuous A M q =
      finiteStageToContinuous A N q := by
  unfold finiteStageToContinuous finiteInflation groupCohomology.map
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    finiteStageCochainMap_refinement]

set_option backward.isDefEq.respectTransparency false in
/-- At each finite stage the map is the actual continuous inflation after the discrete comparison. -/
theorem comparison_comp_finiteStageToContinuous (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    continuousToOrdinary (finiteQuotientTopRep A N) q ≫ finiteStageToContinuous A N q =
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
        (continuousFiniteInflation A N q) := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (TopModuleCat.{u} k) (ComplexShape.up ℕ) q).map
      (ContinuousCohomology.cochainsMap (quotientProjection N) (fixedCoefficientInclusion A N)))
    (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))
  change (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
      (continuousFiniteInflation A N q) ≫
      (((TopRep.homogeneousCochains A.toTopRep).sc q).mapHomologyIso
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).inv =
    (((TopRep.homogeneousCochains (finiteQuotientTopRep A N)).sc q).mapHomologyIso
      (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k))).inv ≫
      HomologicalComplex.homologyMap
        (((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map
            (ContinuousCohomology.cochainsMap (quotientProjection N)
              (fixedCoefficientInclusion A N))) q at h
  unfold continuousToOrdinary finiteStageToContinuous
  rw [Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (continuousToOrdinaryCochains (finiteQuotientTopRep A N)) q),
    ← HomologicalComplex.homologyMap_comp, comparison_comp_finiteStageCochainMap,
    ← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The finite-stage formula as inverse discrete comparison followed by actual inflation. -/
theorem finiteStageToContinuous_eq_inflation (A : DiscreteModule k G)
    (N : OpenNormalSubgroup G) (q : ℕ) :
    finiteStageToContinuous A N q =
      letI : DiscreteTopology (G ⧸ N.toSubgroup) :=
        QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
      inv (continuousToOrdinary (finiteQuotientTopRep A N) q) ≫
        (forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).map
          (continuousFiniteInflation A N q) := by
  let : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology_iff.mpr N.toOpenSubgroup.isOpen
  rw [← comparison_comp_finiteStageToContinuous A N q, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]

end Langlands.Continuous

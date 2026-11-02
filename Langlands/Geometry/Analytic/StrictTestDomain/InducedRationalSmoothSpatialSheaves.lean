import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSpatialSheaves
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothCohomology
import Langlands.Sheaf.Equivariant.SmoothSpatialLocallyConstant

/-! # Full smooth sheaves on actual induced rational spectra -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open Langlands.Sheaf.Equivariant

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

namespace OpenSubgroupTransport.SpatialSheaves

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P} (X : ρ.OpenSubgroupTransport)
  (R : Type u) [CommRing R]

/-- The actual rational unit chart preserves and reflects local fixedness. -/
theorem isLocallyFixedAt_restrict_iff
    {F : (ActionOpens G X.InducedSpectrum)ᵒᵖ ⥤ ModuleCat.{u} R}
    {U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum}
    (s : F.obj (op (unitOpen X U))) (x : X.LocalSpectrum) :
    IsLocallyFixedAt R ((unitFunctor X).op ⋙ F) s x ↔
      IsLocallyFixedAt R F s (X.inducedUnit x) :=
  SpatialInduction.isLocallyFixedAt_restrict_iff
    R X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum s x

/-- Full ordinary rational sheaves are smooth exactly when their unit restrictions are. -/
theorem isSmoothSheaf_restrict_iff
    (F : TopologicalSheaf G X.InducedSpectrum (ModuleCat.{u} R)) :
    IsSmoothSheaf R X.subgroup.toSubgroup X.LocalSpectrum
        ((restrict X (ModuleCat.{u} R)).obj F) ↔
      IsSmoothSheaf R G X.InducedSpectrum F :=
  SpatialInduction.isSmoothSheaf_restrict_iff
    R X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum F

/-- Restriction on all smooth sheaves on the actual rational induced spectrum. -/
def smoothRestrict :
    SmoothTopologicalSheaf R G X.InducedSpectrum ⥤
      SmoothTopologicalSheaf R X.subgroup.toSubgroup X.LocalSpectrum :=
  SpatialInduction.smoothRestrict
    R X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

@[simp]
theorem smoothRestrict_obj_obj (F : SmoothTopologicalSheaf R G X.InducedSpectrum) :
    ((smoothRestrict X R).obj F).obj =
      (restrict X (ModuleCat.{u} R)).obj F.obj := rfl

@[simp]
theorem smoothRestrict_map_hom {F F' : SmoothTopologicalSheaf R G X.InducedSpectrum}
    (f : F ⟶ F') :
    ((smoothRestrict X R).map f).hom =
      (restrict X (ModuleCat.{u} R)).map f.hom := rfl

/-- Forgetting smoothness gives the previously constructed full rational restriction. -/
def smoothRestrictForgetIso :
    smoothRestrict X R ⋙
        Langlands.Sheaf.Equivariant.smoothInclusion R X.subgroup.toSubgroup X.LocalSpectrum ≅
      Langlands.Sheaf.Equivariant.smoothInclusion R G X.InducedSpectrum ⋙ restrict X (ModuleCat.{u} R) :=
  SpatialInduction.smoothRestrictForgetIso
    R X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

/-- The actual rational spatial right Kan extension preserves and reflects smoothness. -/
theorem isSmoothSheaf_induce_iff
    (F : TopologicalSheaf X.subgroup.toSubgroup X.LocalSpectrum (ModuleCat.{u} R)) :
    IsSmoothSheaf R G X.InducedSpectrum
        ((induce X (ModuleCat.{u} R)).obj F) ↔
      IsSmoothSheaf R X.subgroup.toSubgroup X.LocalSpectrum F :=
  SpatialInduction.isSmoothSheaf_induce_iff
    R X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum F

/-- Genuine right Kan induction, retaining the whole local smooth rational sheaf. -/
def smoothInduce :
    SmoothTopologicalSheaf R X.subgroup.toSubgroup X.LocalSpectrum ⥤
      SmoothTopologicalSheaf R G X.InducedSpectrum :=
  SpatialInduction.smoothInduce
    R X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

@[simp]
theorem smoothInduce_obj_obj
    (F : SmoothTopologicalSheaf R X.subgroup.toSubgroup X.LocalSpectrum) :
    ((smoothInduce X R).obj F).obj =
      (induce X (ModuleCat.{u} R)).obj F.obj := rfl

@[simp]
theorem smoothInduce_obj_presheaf
    (F : SmoothTopologicalSheaf R X.subgroup.toSubgroup X.LocalSpectrum) :
    ((smoothInduce X R).obj F).obj.obj =
      (unitFunctor X).op.ran.obj F.obj.obj := rfl

@[simp]
theorem smoothInduce_map_presheaf
    {F F' : SmoothTopologicalSheaf R X.subgroup.toSubgroup X.LocalSpectrum}
    (f : F ⟶ F') :
    ((smoothInduce X R).map f).hom.hom =
      (unitFunctor X).op.ran.map f.hom.hom := rfl

/-- Forgetting smoothness gives the original rational right Kan extension. -/
def smoothInduceForgetIso :
    smoothInduce X R ⋙ Langlands.Sheaf.Equivariant.smoothInclusion R G X.InducedSpectrum ≅
      Langlands.Sheaf.Equivariant.smoothInclusion R X.subgroup.toSubgroup X.LocalSpectrum ⋙
        induce X (ModuleCat.{u} R) :=
  SpatialInduction.smoothInduceForgetIso
    R X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

/-- The complete smooth sheaf categories on the two actual spectra are equivalent. -/
def smoothRestrictionEquivalence :
    SmoothTopologicalSheaf R G X.InducedSpectrum ≌
      SmoothTopologicalSheaf R X.subgroup.toSubgroup X.LocalSpectrum :=
  SpatialInduction.smoothRestrictionEquivalence
    R X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

@[simp]
theorem smoothRestrictionEquivalence_functor :
    (smoothRestrictionEquivalence X R).functor = smoothRestrict X R := rfl

@[simp]
theorem smoothRestrictionEquivalence_inverse :
    (smoothRestrictionEquivalence X R).inverse = smoothInduce X R := rfl

/-- Induction followed by restriction recovers the entire original local smooth sheaf. -/
def smoothRestrictInduceIso :
    smoothInduce X R ⋙ smoothRestrict X R ≅
      𝟭 (SmoothTopologicalSheaf R X.subgroup.toSubgroup X.LocalSpectrum) :=
  (smoothRestrictionEquivalence X R).counitIso

/-- Restriction followed by genuine induction recovers the entire ambient smooth sheaf. -/
def smoothInduceRestrictIso :
    smoothRestrict X R ⋙ smoothInduce X R ≅
      𝟭 (SmoothTopologicalSheaf R G X.InducedSpectrum) :=
  (smoothRestrictionEquivalence X R).unitIso.symm

instance smoothRestrict_full : (smoothRestrict X R).Full :=
  (smoothRestrictionEquivalence X R).fullyFaithfulFunctor.full

instance smoothRestrict_faithful : (smoothRestrict X R).Faithful :=
  (smoothRestrictionEquivalence X R).fullyFaithfulFunctor.faithful

instance smoothInduce_full : (smoothInduce X R).Full :=
  (smoothRestrictionEquivalence X R).fullyFaithfulInverse.full

instance smoothInduce_faithful : (smoothInduce X R).Faithful :=
  (smoothRestrictionEquivalence X R).fullyFaithfulInverse.faithful

/-- Stable neighbourhoods on the actual local and induced rational spectra are equivalent. -/
theorem hasStableNeighbourhoods_iff :
    HasStableNeighbourhoods X.subgroup.toSubgroup X.LocalSpectrum ↔
      HasStableNeighbourhoods G X.InducedSpectrum :=
  SpatialInduction.hasStableNeighbourhoods_iff
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

variable [HasStableNeighbourhoods X.subgroup.toSubgroup X.LocalSpectrum]

/-- Local stable neighbourhoods construct the ambient ones, without a second hypothesis. -/
theorem hasStableNeighbourhoods_induced :
    HasStableNeighbourhoods G X.InducedSpectrum :=
  SpatialInduction.hasStableNeighbourhoods_induced
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

/-- Full smooth coefficient sheaves on the actual induced rational spectrum. -/
def smoothInducedCoefficientFunctor :
    Langlands.SmoothRep.{u, u, u} R G ⥤
      SmoothTopologicalSheaf R G X.InducedSpectrum :=
  SpatialInduction.smoothLocallyConstantFunctor
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum R

/-- Restrict the original smooth coefficients and construct the full local sheaf. -/
def smoothLocalCoefficientFunctor :
    Langlands.SmoothRep.{u, u, u} R G ⥤
      SmoothTopologicalSheaf R X.subgroup.toSubgroup X.LocalSpectrum :=
  Langlands.Induction.smoothRestriction R X.subgroup.toSubgroup ⋙
    LocallyConstantSheaf.smoothFunctor R X.subgroup.toSubgroup X.LocalSpectrum

/-- Forgetting smoothness retains the entire ordinary induced coefficient functor. -/
def smoothInducedCoefficientFunctorForgetIso :
    smoothInducedCoefficientFunctor X R ⋙ Langlands.Sheaf.Equivariant.smoothInclusion R G X.InducedSpectrum ≅
      Langlands.SmoothRep.toRep ⋙ inducedCoefficientFunctor X R :=
  SpatialInduction.smoothLocallyConstantFunctorForgetIso
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum R

/-- Forgetting smoothness retains every original restricted coefficient map and section. -/
def smoothLocalCoefficientFunctorForgetIso :
    smoothLocalCoefficientFunctor X R ⋙
        Langlands.Sheaf.Equivariant.smoothInclusion R X.subgroup.toSubgroup X.LocalSpectrum ≅
      Langlands.SmoothRep.toRep ⋙ localCoefficientFunctor X R :=
  Iso.refl _

/-- Full coefficient-natural smooth restriction comparison on the actual rational spectra. -/
def smoothRestrictCoefficientNatIso :
    smoothInducedCoefficientFunctor X R ⋙ smoothRestrict X R ≅
      smoothLocalCoefficientFunctor X R :=
  SpatialInduction.smoothRestrictLocallyConstantNatIso
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum R

@[simp]
theorem smoothRestrictCoefficientNatIso_hom_app
    (M : Langlands.SmoothRep.{u, u, u} R G)
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant (unitOpen X U).openSet M) (x : U.openSet) :
    LocallyConstant.toFun
      (((smoothRestrictCoefficientNatIso X R).app M).hom.hom.hom.app (op U) s) x =
      s (unitOpenHomeomorph X U x) := rfl

@[simp]
theorem smoothRestrictCoefficientNatIso_inv_app
    (M : Langlands.SmoothRep.{u, u, u} R G)
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant U.openSet M) (x : (unitOpen X U).openSet) :
    LocallyConstant.toFun
      (((smoothRestrictCoefficientNatIso X R).app M).inv.hom.hom.app (op U) s) x =
      s ((unitOpenHomeomorph X U).symm x) := rfl

@[simp]
theorem smoothLocalCoefficientFunctor_map_app
    {M N : Langlands.SmoothRep.{u, u, u} R G} (c : M ⟶ N)
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant U.openSet M) (x : U.openSet) :
    LocallyConstant.toFun
      (((smoothLocalCoefficientFunctor X R).map c).hom.hom.app (op U) s) x =
      c.hom.hom (s x) := rfl

/-- Genuine smooth rational right Kan induction recovers the whole ambient coefficient sheaf. -/
def smoothInduceCoefficientNatIso :
    smoothLocalCoefficientFunctor X R ⋙ smoothInduce X R ≅
      smoothInducedCoefficientFunctor X R :=
  SpatialInduction.smoothInduceLocallyConstantNatIso
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum R

/-- The coefficient functor is the one already used by rational smooth cohomology,
using the constructed ambient stable-neighbourhood proof. -/
def smoothCohomologySheafFunctorIso :
    smoothInducedCoefficientFunctor X R ≅
      (letI := hasStableNeighbourhoods_induced X
       SmoothCohomology.sheafFunctor (R := R) X) :=
  Iso.refl _

/-- The full compact-function comparison now needs only local stable neighbourhoods. -/
def smoothCompactSectionsIso :
    CompactSections.coefficientFunctor (R := R) X ≅
      smoothInducedCoefficientFunctor X R ⋙
        smoothSheafCompactSections R G X.InducedSpectrum := by
  letI := hasStableNeighbourhoods_induced X
  exact SmoothCohomology.compactSectionsIso X

end OpenSubgroupTransport.SpatialSheaves

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

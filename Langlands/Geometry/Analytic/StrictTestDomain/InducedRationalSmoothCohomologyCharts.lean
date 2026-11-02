import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalSmoothCohomology
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalLocalChartComplex

/-! # Actual charts in degree-zero smooth cohomology -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Langlands.Sheaf.Equivariant

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}
  {R : Type u} [CommRing R]

namespace OpenSubgroupTransport.SmoothCohomology

namespace Charts

variable (X : ρ.OpenSubgroupTransport)
  {F : SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R}
  (e : F ≅ CompactSections.supportedModuleFunctor X)

/-- Transport actual chart zero extension through a compact-function identification. -/
def extension (a : G) : CompactSections.chartCoefficientFunctor X a ⟶ F :=
  CompactSections.chartExtensionNatTrans X a ≫ e.inv

/-- Restrict the identified compact function to the actual chart. -/
def restriction (a : G) : F ⟶ CompactSections.chartCoefficientFunctor X a :=
  e.hom ≫ CompactSections.chartRestrictionNatTrans X a

@[simp]
theorem extension_restriction (a : G) :
    extension X e a ≫ restriction X e a =
      𝟙 (CompactSections.chartCoefficientFunctor X a) := by
  simp [extension, restriction, Category.assoc]

/-- The transported projection onto the actual chart summand. -/
def projection (a : G) : F ⟶ F :=
  restriction X e a ≫ extension X e a

@[simp]
theorem projection_toFunctions (a : G) (M : SmoothRep.{u, u, u} R G)
    (s : F.obj M) :
    (e.hom.app M).hom (((projection X e a).app M).hom s) =
      CompactSections.chartPart X a ((e.hom.app M).hom s) := by
  change (e.app M).toLinearEquiv
      ((e.app M).toLinearEquiv.symm
        (CompactSections.chartPart X a ((e.hom.app M).hom s))) = _
  exact (e.app M).toLinearEquiv.apply_symm_apply _

@[simp]
theorem projection_idempotent (a : G) :
    projection X e a ≫ projection X e a = projection X e a := by
  simp [projection, Category.assoc,
    ← Category.assoc (extension X e a) (restriction X e a)]

theorem projection_orthogonal
    (d c : G ⧸ X.subgroup.toSubgroup) (hdc : d ≠ c) :
    projection X e c.out ≫ projection X e d.out = 0 := by
  apply NatTrans.ext
  funext M
  ext s
  apply (e.app M).toLinearEquiv.injective
  change (e.hom.app M).hom
      (((projection X e d.out).app M).hom
        (((projection X e c.out).app M).hom s)) =
    (e.hom.app M).hom 0
  rw [map_zero, projection_toFunctions, projection_toFunctions]
  exact CompactSections.chartPart_out_orthogonal X d c hdc _

/-- Nonzero coset components of the actual compact function representing the vector. -/
def componentSupport (M : SmoothRep.{u, u, u} R G) (s : F.obj M) :
    Set (G ⧸ X.subgroup.toSubgroup) :=
  CompactSections.componentSupport X ((e.hom.app M).hom s).val

theorem finite_componentSupport (M : SmoothRep.{u, u, u} R G) (s : F.obj M) :
    (componentSupport X e M s).Finite :=
  CompactSections.finite_componentSupport X ((e.hom.app M).hom s)

/-- Every finite set containing the actual nonzero components reconstructs the vector. -/
theorem sum_projection_eq (M : SmoothRep.{u, u, u} R G) (s : F.obj M)
    (S : Finset (G ⧸ X.subgroup.toSubgroup))
    (hS : componentSupport X e M s ⊆ (S : Set (G ⧸ X.subgroup.toSubgroup))) :
    (∑ d ∈ S, ((projection X e d.out).app M).hom s) = s := by
  apply (e.app M).toLinearEquiv.injective
  change (e.hom.app M).hom (∑ d ∈ S, ((projection X e d.out).app M).hom s) =
    (e.hom.app M).hom s
  rw [map_sum]
  simp only [projection_toFunctions]
  exact CompactSections.sum_chartPart_eq X _ S hS

/-- A finite actual chart decomposition for every vector, with no uniform support bound. -/
theorem exists_sum_projection (M : SmoothRep.{u, u, u} R G) (s : F.obj M) :
    ∃ S : Finset (G ⧸ X.subgroup.toSubgroup),
      (∑ d ∈ S, ((projection X e d.out).app M).hom s) = s := by
  classical
  exact ⟨(finite_componentSupport X e M s).toFinset,
    sum_projection_eq X e M s _ (by simp)⟩

/-- Extend a function on the actual local spectrum through the constructed chart. -/
def localExtension (a : G) :
    CompactSections.liftedLocalSpectrumCoefficientFunctor X ⟶ F :=
  (CompactSections.localChartCoefficientIso X a).hom ≫ extension X e a

/-- Express the actual chart restriction in local-spectrum coordinates. -/
def localRestriction (a : G) :
    F ⟶ CompactSections.liftedLocalSpectrumCoefficientFunctor X :=
  restriction X e a ≫ (CompactSections.localChartCoefficientIso X a).inv

@[simp]
theorem localExtension_restriction (a : G) :
    localExtension X e a ≫ localRestriction X e a =
      𝟙 (CompactSections.liftedLocalSpectrumCoefficientFunctor X) := by
  simp [localExtension, localRestriction, Category.assoc,
    ← Category.assoc (extension X e a) (restriction X e a)]

theorem localRestriction_extension (a : G) :
    localRestriction X e a ≫ localExtension X e a = projection X e a := by
  simp [localExtension, localRestriction, projection, Category.assoc,
    ← Category.assoc (CompactSections.localChartCoefficientIso X a).inv
      (CompactSections.localChartCoefficientIso X a).hom]

@[simp]
theorem localExtension_toFunctions (a : G) (M : SmoothRep.{u, u, u} R G)
    (s : LocallyConstant X.LocalSpectrum M) :
    (e.hom.app M).hom (((localExtension X e a).app M).hom (ULift.up s)) =
      CompactSections.localChartExtension X a s := by
  change (e.app M).toLinearEquiv
      ((e.app M).toLinearEquiv.symm (CompactSections.localChartExtension X a s)) = _
  exact (e.app M).toLinearEquiv.apply_symm_apply _

@[simp]
theorem localRestriction_apply (a : G) (M : SmoothRep.{u, u, u} R G)
    (s : F.obj M) (z : X.LocalSpectrum) :
    LocallyConstant.toFun
        ((((localRestriction X e a).app M).hom s).down) z =
      ((e.hom.app M).hom s).val (X.inducedChart a z) := rfl

end Charts

variable (X : ρ.OpenSubgroupTransport) [HasStableNeighbourhoods G X.InducedSpectrum]

/-- The actual degree-zero Godement cohomology, forgetting only the group action. -/
def godementZeroModuleFunctor :
    SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R :=
  godementCompactCohomology X 0 ⋙ SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R)

/-- Its full compact-function identification in modules. -/
def godementZeroModuleIso :
    godementZeroModuleFunctor (R := R) X ≅ CompactSections.supportedModuleFunctor X :=
  Functor.isoWhiskerRight (godementCompactCohomologyZeroIso X)
    (SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R))

/-- The actual degree-zero derived compact sections, forgetting only the group action. -/
def compactDerivedZeroModuleFunctor :
    SmoothRep.{u, u, u} R G ⥤ ModuleCat.{u} R :=
  compactDerived X 0 ⋙ SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R)

/-- The derived degree-zero full compact-function identification in modules. -/
def compactDerivedZeroModuleIso :
    compactDerivedZeroModuleFunctor (R := R) X ≅
      CompactSections.supportedModuleFunctor X :=
  Functor.isoWhiskerRight (compactDerivedZeroIso X)
    (SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R))

/-- Actual chart extension into degree-zero smooth Godement cohomology. -/
abbrev godementChartExtension (a : G) :=
  Charts.extension X (godementZeroModuleIso (R := R) X) a

/-- Actual chart restriction from degree-zero smooth Godement cohomology. -/
abbrev godementChartRestriction (a : G) :=
  Charts.restriction X (godementZeroModuleIso (R := R) X) a

/-- The actual chart summand projection in degree-zero Godement cohomology. -/
abbrev godementChartProjection (a : G) :=
  Charts.projection X (godementZeroModuleIso (R := R) X) a

/-- Actual local-spectrum extension into degree-zero smooth Godement cohomology. -/
abbrev godementLocalExtension (a : G) :=
  Charts.localExtension X (godementZeroModuleIso (R := R) X) a

/-- Actual local-spectrum restriction from degree-zero smooth Godement cohomology. -/
abbrev godementLocalRestriction (a : G) :=
  Charts.localRestriction X (godementZeroModuleIso (R := R) X) a

/-- Actual chart extension into degree-zero derived compact sections. -/
abbrev compactDerivedChartExtension (a : G) :=
  Charts.extension X (compactDerivedZeroModuleIso (R := R) X) a

/-- Actual chart restriction from degree-zero derived compact sections. -/
abbrev compactDerivedChartRestriction (a : G) :=
  Charts.restriction X (compactDerivedZeroModuleIso (R := R) X) a

/-- The actual chart summand projection in degree-zero derived compact sections. -/
abbrev compactDerivedChartProjection (a : G) :=
  Charts.projection X (compactDerivedZeroModuleIso (R := R) X) a

/-- Actual local-spectrum extension into degree-zero derived compact sections. -/
abbrev compactDerivedLocalExtension (a : G) :=
  Charts.localExtension X (compactDerivedZeroModuleIso (R := R) X) a

/-- Actual local-spectrum restriction from degree-zero derived compact sections. -/
abbrev compactDerivedLocalRestriction (a : G) :=
  Charts.localRestriction X (compactDerivedZeroModuleIso (R := R) X) a

/-- The two degree-zero module realizations compare by the original compact functions. -/
def godementDerivedZeroModuleIso :
    godementZeroModuleFunctor (R := R) X ≅ compactDerivedZeroModuleFunctor X :=
  godementZeroModuleIso X ≪≫ (compactDerivedZeroModuleIso X).symm

/-- This is exactly the original degree-zero comparison with the action forgotten. -/
theorem godementDerivedZeroModuleIso_eq :
    godementDerivedZeroModuleIso (R := R) X =
      Functor.isoWhiskerRight (godementDerivedZeroIso X)
        (SmoothRep.toRep ⋙ forget₂ (Rep R G) (ModuleCat R)) := rfl

@[reassoc (attr := simp)]
theorem chartExtension_comparison (a : G) :
    godementChartExtension (R := R) X a ≫ (godementDerivedZeroModuleIso X).hom =
      compactDerivedChartExtension X a := by
  simp [godementChartExtension, compactDerivedChartExtension, Charts.extension,
    godementDerivedZeroModuleIso, Category.assoc,
    ← Category.assoc (godementZeroModuleIso X).inv (godementZeroModuleIso X).hom]

@[reassoc (attr := simp)]
theorem chartRestriction_comparison (a : G) :
    (godementDerivedZeroModuleIso (R := R) X).hom ≫
        compactDerivedChartRestriction X a = godementChartRestriction X a := by
  simp [godementChartRestriction, compactDerivedChartRestriction, Charts.restriction,
    godementDerivedZeroModuleIso, Category.assoc,
    ← Category.assoc (compactDerivedZeroModuleIso X).inv
      (compactDerivedZeroModuleIso X).hom]

end OpenSubgroupTransport.SmoothCohomology

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

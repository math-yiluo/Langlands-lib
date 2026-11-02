import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCharts
import Langlands.Sheaf.Equivariant.SpatialLocallyConstant

/-! # Spatial sheaf equivalence on actual induced rational spectra -/

noncomputable section

universe u v a b r w

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Topology
open Langlands.Sheaf.Equivariant

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

namespace OpenSubgroupTransport.SpatialSheaves

section General

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P} (X : ρ.OpenSubgroupTransport)

/-- The actual unit chart on the transport categories of the two spectra. -/
abbrev unitFunctor :
    ActionOpens X.subgroup.toSubgroup X.LocalSpectrum ⥤
      ActionOpens G X.InducedSpectrum :=
  SpatialInduction.unitFunctor X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

/-- The image of an arbitrary local open in the actual induced rational spectrum. -/
abbrev unitOpen (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum) :
    ActionOpens G X.InducedSpectrum :=
  (unitFunctor X).obj U

@[simp]
theorem unitOpen_carrier (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum) :
    ((unitOpen X U).openSet : Set X.InducedSpectrum) =
      X.inducedUnit '' (U.openSet : Set X.LocalSpectrum) := rfl

@[simp]
theorem mem_unitOpen (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (x : X.LocalSpectrum) :
    X.inducedUnit x ∈ (unitOpen X U).openSet ↔ x ∈ U.openSet :=
  SpatialInduction.mem_unitOpen X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum U x

/-- The entire local spectrum gives exactly the distinguished rational chart. -/
theorem unitOpen_top :
    (unitOpen X ActionOpens.top).openSet = X.inducedChartDomain 1 := by
  apply Opens.ext
  change X.inducedUnit '' Set.univ = Set.range (X.inducedChart 1)
  rw [Set.image_univ, X.inducedChart_one]

@[simp]
theorem unitFunctor_map_label
    {U V : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum} (f : U ⟶ V) :
    ((unitFunctor X).map f).label = (f.label : G) := rfl

/-- Preimage of any ambient open under an actual translated rational chart. -/
abbrev chartPreimage (g : G) (U : ActionOpens G X.InducedSpectrum) :
    ActionOpens X.subgroup.toSubgroup X.LocalSpectrum :=
  SpatialInduction.chartPreimage X.subgroup.toSubgroup X.LocalSpectrum g U

@[simp]
theorem mem_chartPreimage (g : G) (U : ActionOpens G X.InducedSpectrum)
    (x : X.LocalSpectrum) :
    x ∈ (chartPreimage X g U).openSet ↔ X.inducedChart g x ∈ U.openSet := Iff.rfl

/-- The covering arrows use the actual group labels of the translated charts. -/
abbrev chartArrow (g : G) (U : ActionOpens G X.InducedSpectrum) :
    unitOpen X (chartPreimage X g U) ⟶ U :=
  SpatialInduction.chartArrow X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum g U

@[simp]
theorem chartArrow_label (g : G) (U : ActionOpens G X.InducedSpectrum) :
    (chartArrow X g U).label = g := rfl

variable (A : Type a) [Category.{b} A]

/-- Restrict full equivariant sheaves to the actual rational quotient spectrum. -/
def restrict :
    TopologicalSheaf G X.InducedSpectrum A ⥤
      TopologicalSheaf X.subgroup.toSubgroup X.LocalSpectrum A :=
  SpatialInduction.restrict X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum A

instance restrict_full : (restrict X A).Full := by
  dsimp [restrict]
  infer_instance

instance restrict_faithful : (restrict X A).Faithful := by
  dsimp [restrict]
  infer_instance

@[simp]
theorem restrict_obj_obj (F : TopologicalSheaf G X.InducedSpectrum A) :
    ((restrict X A).obj F).obj = (unitFunctor X).op ⋙ F.obj := rfl

@[simp]
theorem restrict_obj_obj_obj (F : TopologicalSheaf G X.InducedSpectrum A)
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum) :
    ((restrict X A).obj F).obj.obj (op U) = F.obj.obj (op (unitOpen X U)) := rfl

@[simp]
theorem restrict_obj_obj_map (F : TopologicalSheaf G X.InducedSpectrum A)
    {U V : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum} (f : U ⟶ V) :
    ((restrict X A).obj F).obj.map f.op =
      F.obj.map ((unitFunctor X).map f).op := rfl

@[simp]
theorem restrict_map_hom_app {F F' : TopologicalSheaf G X.InducedSpectrum A}
    (f : F ⟶ F') (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum) :
    ((restrict X A).map f).hom.app (op U) = f.hom.app (op (unitOpen X U)) := rfl

section Limits

variable [∀ U : (ActionOpens G X.InducedSpectrum)ᵒᵖ,
  HasLimitsOfShape (StructuredArrow U (unitFunctor X).op) A]

/-- Genuine right Kan extension from the actual rational unit-chart subsite. -/
def induce :
    TopologicalSheaf X.subgroup.toSubgroup X.LocalSpectrum A ⥤
      TopologicalSheaf G X.InducedSpectrum A :=
  SpatialInduction.induce X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum A

@[simp]
theorem induce_obj_obj
    (F : TopologicalSheaf X.subgroup.toSubgroup X.LocalSpectrum A) :
    ((induce X A).obj F).obj = (unitFunctor X).op.ran.obj F.obj := rfl

@[simp]
theorem induce_map_hom {F F' : TopologicalSheaf X.subgroup.toSubgroup X.LocalSpectrum A}
    (f : F ⟶ F') :
    ((induce X A).map f).hom = (unitFunctor X).op.ran.map f.hom := rfl

/-- All equivariant sheaves on the actual two different spectra are equivalent. -/
def restrictionEquivalence :
    TopologicalSheaf G X.InducedSpectrum A ≌
      TopologicalSheaf X.subgroup.toSubgroup X.LocalSpectrum A :=
  SpatialInduction.restrictionEquivalence
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum A

@[simp]
theorem restrictionEquivalence_functor :
    (restrictionEquivalence X A).functor = restrict X A := rfl

@[simp]
theorem restrictionEquivalence_inverse :
    (restrictionEquivalence X A).inverse = induce X A := rfl

/-- The entire original subgroup sheaf is recovered, naturally in all morphisms. -/
def restrictInduceIso :
    induce X A ⋙ restrict X A ≅
      𝟭 (TopologicalSheaf X.subgroup.toSubgroup X.LocalSpectrum A) :=
  (restrictionEquivalence X A).counitIso

/-- The entire original ambient sheaf is recovered, naturally in all morphisms. -/
def induceRestrictIso :
    restrict X A ⋙ induce X A ≅ 𝟭 (TopologicalSheaf G X.InducedSpectrum A) :=
  (restrictionEquivalence X A).unitIso.symm

end Limits

/-- Each actual local open is homeomorphic to its actual unit-chart image. -/
abbrev unitOpenHomeomorph (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum) :
    U.openSet ≃ₜ (unitOpen X U).openSet :=
  SpatialInduction.unitOpenHomeomorph
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum U

@[simp]
theorem unitOpenHomeomorph_apply_coe
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum) (x : U.openSet) :
    (unitOpenHomeomorph X U x : X.InducedSpectrum) = X.inducedUnit x.val := rfl

variable {R : Type r} [CommRing R] {M : Type w} [AddCommGroup M] [Module R M]

/-- All local coefficient sections, with the actual restriction and its inverse. -/
abbrev unitSectionsLinearEquiv
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum) :
    LocallyConstant (unitOpen X U).openSet M ≃ₗ[R] LocallyConstant U.openSet M :=
  SpatialInduction.unitSectionsLinearEquiv
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum U

@[simp]
theorem unitSectionsLinearEquiv_apply
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant (unitOpen X U).openSet M) (x : U.openSet) :
    unitSectionsLinearEquiv (R := R) X U s x = s (unitOpenHomeomorph X U x) := rfl

@[simp]
theorem unitSectionsLinearEquiv_symm_apply
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant U.openSet M) (x : (unitOpen X U).openSet) :
    (unitSectionsLinearEquiv (R := R) X U).symm s x =
      s ((unitOpenHomeomorph X U).symm x) := rfl

/-- Each original subgroup-labelled inverse-coefficient pullback is retained. -/
theorem unitSectionsLinearEquiv_pullback (τ : Representation R G M)
    {U V : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum} (f : U ⟶ V)
    (s : LocallyConstant (unitOpen X V).openSet M) :
    unitSectionsLinearEquiv (R := R) X U
        (LocallyConstantSheaf.pullback τ ((unitFunctor X).map f) s) =
      LocallyConstantSheaf.pullback (τ.comp X.subgroup.toSubgroup.subtype) f
        (unitSectionsLinearEquiv (R := R) X V s) :=
  SpatialInduction.unitSectionsLinearEquiv_pullback
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum τ f s

/-- Arbitrary original coefficient linear maps commute with the comparison. -/
theorem unitSectionsLinearEquiv_map {N : Type w} [AddCommGroup N] [Module R N]
    (c : M →ₗ[R] N) (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant (unitOpen X U).openSet M) :
    unitSectionsLinearEquiv (R := R) X U (LocallyConstant.mapₗ R c s) =
      LocallyConstant.mapₗ R c (unitSectionsLinearEquiv (R := R) X U s) := rfl

end General

section Coefficients

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P} (X : ρ.OpenSubgroupTransport)
  (R : Type r) [CommRing R]

/-- The full ordinary-open coefficient sheaf on the actual induced rational spectrum. -/
def inducedCoefficientFunctor :
    Rep.{w} R G ⥤ TopologicalSheaf G X.InducedSpectrum (ModuleCat.{max u w} R) :=
  LocallyConstantSheaf.functor R G X.InducedSpectrum

/-- The full local coefficient sheaf, with the original ambient action restricted to H. -/
def localCoefficientFunctor :
    Rep.{w} R G ⥤
      TopologicalSheaf X.subgroup.toSubgroup X.LocalSpectrum (ModuleCat.{max u w} R) :=
  Rep.resFunctor X.subgroup.toSubgroup.subtype ⋙
    LocallyConstantSheaf.functor R X.subgroup.toSubgroup X.LocalSpectrum

/-- The actual module limits needed by this rational-spectrum right Kan extension exist. -/
instance unitChartModuleLimits (U : (ActionOpens G X.InducedSpectrum)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (unitFunctor X).op) (ModuleCat.{max u w} R) :=
  ModuleCat.hasLimitsOfShape

/-- Full coefficient-natural restriction comparison on the actual spectra. -/
def restrictCoefficientNatIso :
    inducedCoefficientFunctor X R ⋙ restrict X (ModuleCat.{max u w} R) ≅
      localCoefficientFunctor X R :=
  SpatialInduction.restrictLocallyConstantNatIso
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

@[simp]
theorem restrictCoefficientNatIso_hom_app (M : Rep.{w} R G)
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant (unitOpen X U).openSet M) (x : U.openSet) :
    LocallyConstant.toFun
      (((restrictCoefficientNatIso X R).app M).hom.hom.app (op U) s) x =
      s (unitOpenHomeomorph X U x) := rfl

@[simp]
theorem restrictCoefficientNatIso_inv_app (M : Rep.{w} R G)
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant U.openSet M) (x : (unitOpen X U).openSet) :
    LocallyConstant.toFun
      (((restrictCoefficientNatIso X R).app M).inv.hom.app (op U) s) x =
      s ((unitOpenHomeomorph X U).symm x) := rfl

/-- Pointwise evaluation shows that every original ambient intertwiner is retained. -/
@[simp]
theorem localCoefficientFunctor_map_app {M N : Rep.{w} R G} (c : M ⟶ N)
    (U : ActionOpens X.subgroup.toSubgroup X.LocalSpectrum)
    (s : LocallyConstant U.openSet M) (x : U.openSet) :
    LocallyConstant.toFun
      (((localCoefficientFunctor X R).map c).hom.app (op U) s) x = c.hom (s x) := rfl

/-- The converse comparison uses the genuine spatial right Kan extension. -/
def induceCoefficientNatIso :
    localCoefficientFunctor X R ⋙ induce X (ModuleCat.{max u w} R) ≅
      inducedCoefficientFunctor X R :=
  SpatialInduction.induceLocallyConstantNatIso
    X.subgroup.toSubgroup X.subgroup.isOpen' X.LocalSpectrum

end Coefficients

end OpenSubgroupTransport.SpatialSheaves

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

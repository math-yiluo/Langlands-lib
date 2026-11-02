import Langlands.Geometry.EtaleTransportAbelian
import Langlands.Geometry.EtaleTransportSmoothSections
import Langlands.Cohomology.DerivedPlusNaturality

/-! # Derived smooth sections of actual small-etale transport sheaves -/

noncomputable section

universe u w wS wT uK vK

namespace Langlands.Geometry.EtaleTransport.DerivedSmoothSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {Y : Scheme.{u}} {G : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ) [Small.{u} G]
variable (R : Type u) [CommRing R]

/-- Right-derived smooth sections of actual algebraic transport sheaves. -/
def cohomology (q : ℕ) : ModuleSheaf.{u, w, u, u} ρ R ⥤ SmoothRep.{u, w, u} R G :=
  (SmoothSections.sections ρ R).rightDerived q

/-- Apply the smooth section functor to a chosen transport injective resolution. -/
def complex (F : ModuleSheaf.{u, w, u, u} ρ R) : CochainComplex (SmoothRep.{u, w, u} R G) ℕ :=
  (SmoothSections.complex ρ R (ComplexShape.up ℕ)).obj (moduleSheafInjectiveResolution ρ R F).cocomplex

/-- The section complex of an injective resolution is functorial after homotopy. -/
def homotopyFunctor :
    ModuleSheaf.{u, w, u, u} ρ R ⥤ HomotopyCategory (SmoothRep.{u, w, u} R G) (ComplexShape.up ℕ) :=
  (SmoothSections.sections ρ R).rightDerivedToHomotopyCategory

/-- The chosen strict complex represents the homotopy-valued derived functor. -/
def complexIso (F : ModuleSheaf.{u, w, u, u} ρ R) :
    (homotopyFunctor ρ R).obj F ≅
      (HomotopyCategory.quotient _ _).obj (complex ρ R F) :=
  (moduleSheafInjectiveResolution ρ R F).isoRightDerivedToHomotopyCategoryObj _

/-- Every genuine transport-sheaf injective resolution computes cohomology in `SmoothRep`. -/
def cohomologyResolutionIso {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) (q : ℕ) :
    (cohomology ρ R q).obj F ≅
      ((SmoothSections.complex ρ R (ComplexShape.up ℕ)).obj I.cocomplex).homology q :=
  I.isoRightDerivedObj (SmoothSections.sections ρ R) q

/-- Zeroth smooth-representation-valued cohomology is the actual smooth section representation. -/
def cohomologyZeroIso : cohomology ρ R 0 ≅ SmoothSections.sections ρ R :=
  (SmoothSections.sections ρ R).rightDerivedZeroIsoSelf

/-- Injective transport sheaves have no positive smooth section cohomology. -/
theorem isZero_cohomology_succ_of_injective
    (F : ModuleSheaf.{u, w, u, u} ρ R) [Injective F] (q : ℕ) :
    IsZero ((cohomology ρ R (q + 1)).obj F) :=
  (SmoothSections.sections ρ R).isZero_rightDerived_obj_injective_succ q F

section BoundedBelow

variable [HasDerivedCategory.{wS} (ModuleSheaf.{u, w, u, u} ρ R)]
  [HasDerivedCategory.{wT} (SmoothRep.{u, w, u} R G)]

/-- The actual right-derived functor has values in the derived category of smooth representations. -/
def rightDerivedFunctor :
    DerivedCategory.Plus (ModuleSheaf.{u, w, u, u} ρ R) ⥤
      DerivedCategory.Plus (SmoothRep.{u, w, u} R G) :=
  (SmoothSections.sections ρ R).rightDerivedFunctorPlus

/-- Derived sections of a sheaf placed in degree zero, as a derived representation object. -/
def derivedSections :
    ModuleSheaf.{u, w, u, u} ρ R ⥤ DerivedCategory.Plus (SmoothRep.{u, w, u} R G) :=
  Langlands.Cohomology.DerivedPlus.derivedComplex (SmoothSections.sections ρ R)

/-- A bounded-below strict representative from an actual transport injective resolution. -/
def complexPlus (F : ModuleSheaf.{u, w, u, u} ρ R) :
    CochainComplex.Plus (SmoothRep.{u, w, u} R G) :=
  (SmoothSections.sections ρ R).mapCochainComplexPlus.obj
    (Langlands.Cohomology.DerivedPlus.resolutionPlus (moduleSheafInjectiveResolution ρ R F))

/-- Every transport injective resolution represents the derived section object. -/
def resolutionIso {F : ModuleSheaf.{u, w, u, u} ρ R} (I : InjectiveResolution F) :
    (derivedSections ρ R).obj F ≅ DerivedCategory.Plus.Q.obj
      ((SmoothSections.sections ρ R).mapCochainComplexPlus.obj
        (Langlands.Cohomology.DerivedPlus.resolutionPlus I)) :=
  Langlands.Cohomology.DerivedPlus.derivedComplexIso (SmoothSections.sections ρ R) I

/-- The chosen bounded-below smooth representation complex computes derived sections. -/
def complexPlusIso (F : ModuleSheaf.{u, w, u, u} ρ R) :
    (derivedSections ρ R).obj F ≅ DerivedCategory.Plus.Q.obj (complexPlus ρ R F) :=
  resolutionIso ρ R (moduleSheafInjectiveResolution ρ R F)

/-- A chosen strict lift of a sheaf map; the functor laws hold after localization. -/
def complexPlusMap {F H : ModuleSheaf.{u, w, u, u} ρ R} (f : F ⟶ H) :
    complexPlus ρ R F ⟶ complexPlus ρ R H :=
  (SmoothSections.sections ρ R).mapCochainComplexPlus.map
    (Langlands.Cohomology.DerivedPlus.resolutionPlusMap
      (Langlands.Cohomology.DerivedPlus.descHom f
        (moduleSheafInjectiveResolution ρ R F) (moduleSheafInjectiveResolution ρ R H)))

/-- Resolution comparisons intertwine every compatible map of injective resolutions. -/
@[reassoc]
theorem resolutionIso_hom_naturality {F H : ModuleSheaf.{u, w, u, u} ρ R} {f : F ⟶ H}
    {I : InjectiveResolution F} {J : InjectiveResolution H}
    (φ : InjectiveResolution.Hom I J f) :
    (derivedSections ρ R).map f ≫ (resolutionIso ρ R J).hom =
      (resolutionIso ρ R I).hom ≫ DerivedCategory.Plus.Q.map
        ((SmoothSections.sections ρ R).mapCochainComplexPlus.map
          (Langlands.Cohomology.DerivedPlus.resolutionPlusMap φ)) :=
  Langlands.Cohomology.DerivedPlus.derivedComplexIso_hom_naturality
    (SmoothSections.sections ρ R) φ

/-- Chosen strict maps recover the actual derived-section maps after localization. -/
@[reassoc]
theorem complexPlusIso_hom_naturality {F H : ModuleSheaf.{u, w, u, u} ρ R} (f : F ⟶ H) :
    (derivedSections ρ R).map f ≫ (complexPlusIso ρ R H).hom =
      (complexPlusIso ρ R F).hom ≫ DerivedCategory.Plus.Q.map (complexPlusMap ρ R f) :=
  resolutionIso_hom_naturality ρ R
    (Langlands.Cohomology.DerivedPlus.descHom f
      (moduleSheafInjectiveResolution ρ R F) (moduleSheafInjectiveResolution ρ R H))

/-- Nonnegative cohomology of the derived object is the smooth-representation-valued derived functor. -/
def homologyNatIso (q : ℕ) :
    derivedSections ρ R ⋙ DerivedCategory.Plus.homologyFunctor (SmoothRep.{u, w, u} R G) q ≅
      cohomology ρ R q :=
  Langlands.Cohomology.DerivedPlus.homologyNatIso (SmoothSections.sections ρ R) q

/-- The natural comparison can be computed with any transport injective resolution. -/
theorem homologyNatIso_hom_app {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) (q : ℕ) :
    (homologyNatIso ρ R q).hom.app F =
      (Langlands.Cohomology.DerivedPlus.homologyIso (SmoothSections.sections ρ R) I q).hom :=
  Langlands.Cohomology.DerivedPlus.homologyNatIso_hom_app (SmoothSections.sections ρ R) q I

/-- Zeroth cohomology of the derived representation object is actual smooth global sections. -/
def homologyZeroIso :
    derivedSections ρ R ⋙ DerivedCategory.Plus.homologyFunctor (SmoothRep.{u, w, u} R G) 0 ≅
      SmoothSections.sections ρ R :=
  homologyNatIso ρ R 0 ≪≫ cohomologyZeroIso ρ R

/-- Derived sections of a sheaf have no negative cohomology. -/
theorem isZero_homology_of_neg (F : ModuleSheaf.{u, w, u, u} ρ R) {q : ℤ} (hq : q < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (SmoothRep.{u, w, u} R G) q).obj
      ((derivedSections ρ R).obj F)) :=
  Langlands.Cohomology.DerivedPlus.isZero_homology_of_neg (SmoothSections.sections ρ R) F hq

/-- Injective transport sheaves have no positive cohomology in the derived smooth object. -/
theorem isZero_homology_succ_of_injective
    (F : ModuleSheaf.{u, w, u, u} ρ R) [Injective F] (q : ℕ) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (SmoothRep.{u, w, u} R G) (q + 1 : ℕ)).obj
      ((derivedSections ρ R).obj F)) :=
  IsZero.of_iso (isZero_cohomology_succ_of_injective ρ R F q)
    ((homologyNatIso ρ R (q + 1)).app F)

/-- Coefficient diagrams and their maps induce actual derived smooth representation diagrams. -/
def diagramFunctor (K : Type uK) [Category.{vK} K] :
    (K ⥤ ModuleSheaf.{u, w, u, u} ρ R) ⥤ (K ⥤ DerivedCategory.Plus (SmoothRep.{u, w, u} R G)) :=
  (Functor.whiskeringRight K _ _).obj (derivedSections ρ R)

end BoundedBelow

end Langlands.Geometry.EtaleTransport.DerivedSmoothSections

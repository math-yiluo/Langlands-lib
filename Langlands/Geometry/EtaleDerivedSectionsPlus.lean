import Langlands.Geometry.EtaleDerivedSections
import Langlands.Cohomology.DerivedPlusNaturality

/-! # Bounded-below derived global sections on the actual small-etale site -/

noncomputable section

universe u wS wT uK vK

namespace Langlands.Geometry.EtaleDerivedSectionsPlus

open CategoryTheory CategoryTheory.Limits
open EtaleDerivedSections

variable (X : AlgebraicGeometry.Scheme.{u}) (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wS} (ModuleSheaf X R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]

/-- The actual right-derived global-section functor on bounded-below derived
categories of small-etale sheaves and modules. -/
def rightDerivedFunctor :
    DerivedCategory.Plus (ModuleSheaf X R) ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  (sections X R).rightDerivedFunctorPlus

/-- Place a coefficient sheaf in degree zero and apply derived global sections. -/
def derivedSections : ModuleSheaf X R ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  Langlands.Cohomology.DerivedPlus.derivedComplex (sections X R)

/-- Global sections of the integer-indexed extension of a chosen injective
resolution, as an actual bounded-below cochain complex. -/
def complex (F : ModuleSheaf X R) : CochainComplex.Plus (ModuleCat.{u} R) :=
  (sections X R).mapCochainComplexPlus.obj
    (Langlands.Cohomology.DerivedPlus.resolutionPlus (injectiveResolution F))

/-- Any injective resolution computes the derived-section object. -/
def resolutionIso {F : ModuleSheaf X R} (I : InjectiveResolution F) :
    (derivedSections X R).obj F ≅
      DerivedCategory.Plus.Q.obj ((sections X R).mapCochainComplexPlus.obj
        (Langlands.Cohomology.DerivedPlus.resolutionPlus I)) :=
  Langlands.Cohomology.DerivedPlus.derivedComplexIso (sections X R) I

/-- The chosen section complex represents derived global sections. -/
def complexIso (F : ModuleSheaf X R) :
    (derivedSections X R).obj F ≅ DerivedCategory.Plus.Q.obj (complex X R F) :=
  resolutionIso X R (injectiveResolution F)

/-- A chosen resolution lift of a coefficient map, followed by global sections.
Its strict functor laws are only asserted after localization. -/
def complexMap {F G : ModuleSheaf X R} (f : F ⟶ G) :
    complex X R F ⟶ complex X R G :=
  (sections X R).mapCochainComplexPlus.map
    (Langlands.Cohomology.DerivedPlus.resolutionPlusMap
      (Langlands.Cohomology.DerivedPlus.descHom f
        (injectiveResolution F) (injectiveResolution G)))

/-- Naturality for any compatible map between injective resolutions. -/
@[reassoc]
theorem resolutionIso_hom_naturality {F G : ModuleSheaf X R} {f : F ⟶ G}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : InjectiveResolution.Hom I J f) :
    (derivedSections X R).map f ≫ (resolutionIso X R J).hom =
      (resolutionIso X R I).hom ≫ DerivedCategory.Plus.Q.map
        ((sections X R).mapCochainComplexPlus.map
          (Langlands.Cohomology.DerivedPlus.resolutionPlusMap φ)) :=
  Langlands.Cohomology.DerivedPlus.derivedComplexIso_hom_naturality (sections X R) φ

/-- The chosen complex maps recover all coefficient maps after localization. -/
@[reassoc]
theorem complexIso_hom_naturality {F G : ModuleSheaf X R} (f : F ⟶ G) :
    (derivedSections X R).map f ≫ (complexIso X R G).hom =
      (complexIso X R F).hom ≫ DerivedCategory.Plus.Q.map (complexMap X R f) :=
  resolutionIso_hom_naturality X R
    (Langlands.Cohomology.DerivedPlus.descHom f
      (injectiveResolution F) (injectiveResolution G))

/-- Nonnegative cohomology recovers the existing ordinary etale-cohomology
functor, naturally in every coefficient map. -/
def homologyNatIso (q : ℕ) :
    derivedSections X R ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ≅
      cohomology X R q :=
  Langlands.Cohomology.DerivedPlus.homologyNatIso (sections X R) q

/-- The natural cohomology comparison can be computed with any resolution. -/
theorem homologyNatIso_hom_app {F : ModuleSheaf X R}
    (I : InjectiveResolution F) (q : ℕ) :
    (homologyNatIso X R q).hom.app F =
      (Langlands.Cohomology.DerivedPlus.homologyIso (sections X R) I q).hom :=
  Langlands.Cohomology.DerivedPlus.homologyNatIso_hom_app (sections X R) q I

/-- Zeroth cohomology of derived global sections is ordinary global sections. -/
def homologyZeroIso :
    derivedSections X R ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0 ≅
      sections X R :=
  homologyNatIso X R 0 ≪≫ cohomologyZeroIso X R

/-- Derived global sections of a sheaf have zero cohomology in negative degrees. -/
theorem isZero_homology_of_neg (F : ModuleSheaf X R) {q : ℤ} (hq : q < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).obj
      ((derivedSections X R).obj F)) :=
  Langlands.Cohomology.DerivedPlus.isZero_homology_of_neg (sections X R) F hq

/-- Coefficient diagrams and maps of diagrams give actual diagrams in the
bounded-below derived category. -/
def diagramFunctor (K : Type uK) [Category.{vK} K] :
    (K ⥤ ModuleSheaf X R) ⥤ (K ⥤ DerivedCategory.Plus (ModuleCat.{u} R)) :=
  (Functor.whiskeringRight K (ModuleSheaf X R)
    (DerivedCategory.Plus (ModuleCat.{u} R))).obj (derivedSections X R)

end Langlands.Geometry.EtaleDerivedSectionsPlus

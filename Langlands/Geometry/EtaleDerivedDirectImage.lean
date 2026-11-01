import Langlands.Geometry.EtaleInverseImageExact
import Langlands.Geometry.EtaleDerivedSectionsPlus
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Actual higher and bounded-below derived geometric direct images -/

noncomputable section

universe u wX wZ uK vK

namespace Langlands.Geometry.EtaleDerivedDirectImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Shimura.Coefficients
open EtaleDirectImage EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

instance directImage_preservesLimits :
    PreservesLimitsOfSize.{u, u} (directImage f (ModuleCat.{u} R)) :=
  (inverseImageAdjunction f R).rightAdjoint_preservesLimits

instance directImage_preservesFiniteLimits :
    PreservesFiniteLimits (directImage f (ModuleCat.{u} R)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u}
  intro J _ _
  infer_instance

/-- Actual direct image preserves injectives because its constructed left
adjoint is exact. Direct image itself need not be exact. -/
instance directImage_preservesInjectives :
    (directImage f (ModuleCat.{u} R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (inverseImageAdjunction f R)

/-- Apply actual direct image to the chosen injective resolution on Z. -/
def resolutionComplex (F : ModuleSheaf Z R) : CochainComplex (ModuleSheaf X R) ℕ :=
  ((directImage f (ModuleCat.{u} R)).mapHomologicalComplex _).obj
    (injectiveResolution F).cocomplex

theorem resolutionComplex_injective (F : ModuleSheaf Z R) (n : ℕ) :
    Injective ((resolutionComplex f R F).X n) :=
  (directImage f (ModuleCat.{u} R)).injective_obj_of_injective
    ((injectiveResolution F).injective n)

/-- The actual right-derived direct-image object in the homotopy category. -/
def homotopyDirectImage :
    ModuleSheaf Z R ⥤ HomotopyCategory (ModuleSheaf X R) (ComplexShape.up ℕ) :=
  (directImage f (ModuleCat.{u} R)).rightDerivedToHomotopyCategory

/-- Higher geometric direct image on the actual small-etale sites. -/
def higherDirectImage (q : ℕ) : ModuleSheaf Z R ⥤ ModuleSheaf X R :=
  (directImage f (ModuleCat.{u} R)).rightDerived q

def resolutionComplexIso (F : ModuleSheaf Z R) :
    (homotopyDirectImage f R).obj F ≅
      (HomotopyCategory.quotient _ _).obj (resolutionComplex f R F) :=
  (injectiveResolution F).isoRightDerivedToHomotopyCategoryObj _

def higherDirectImageIso (F : ModuleSheaf Z R) (q : ℕ) :
    (higherDirectImage f R q).obj F ≅ (resolutionComplex f R F).homology q :=
  (injectiveResolution F).isoRightDerivedObj _ q

/-- Zeroth higher direct image recovers the same geometric direct image. -/
def higherDirectImageZeroIso :
    higherDirectImage f R 0 ≅ directImage f (ModuleCat.{u} R) :=
  (directImage f (ModuleCat.{u} R)).rightDerivedZeroIsoSelf

/-- Direct image sections at the terminal object agree with sections on Z,
using the actual preserved terminal object under geometric base change. -/
def terminalSectionsIso :
    directImage f (ModuleCat.{u} R) ⋙
        (sheafSections X.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ X.Etale)) ≅
      (sheafSections Z.smallEtaleTopology (ModuleCat.{u} R)).obj (op (⊤_ Z.Etale)) :=
  NatIso.ofComponents (fun F =>
    F.obj.mapIso (PreservesTerminal.iso (etaleObjectPullback f)).op.symm)
    (fun {_F _G} a => (a.hom.naturality _).symm)

/-- The actual canonical global-section comparison for geometric direct image. -/
def directImageSectionsIso :
    directImage f (ModuleCat.{u} R) ⋙ sections X R ≅ sections Z R :=
  Functor.isoWhiskerLeft (directImage f (ModuleCat.{u} R)) (sectionsIso X R) ≪≫
    terminalSectionsIso f R ≪≫ (sectionsIso Z R).symm

/-- Deriving the composite of direct image and sections agrees with
cohomology on Z. This does not interchange sections with higher direct image. -/
def compositeSectionsRightDerivedIso (q : ℕ) :
    (directImage f (ModuleCat.{u} R) ⋙ sections X R).rightDerived q ≅ cohomology Z R q where
  hom := NatTrans.rightDerived (directImageSectionsIso f R).hom q
  inv := NatTrans.rightDerived (directImageSectionsIso f R).inv q
  hom_inv_id := by
    rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id, NatTrans.rightDerived_id]
    rfl

section DerivedPlus

variable [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wX} (ModuleSheaf X R)]

/-- The actual right-derived direct-image functor on bounded-below derived
categories. The localization universes on X and Z are independent. -/
def rightDerivedFunctor :
    DerivedCategory.Plus (ModuleSheaf Z R) ⥤ DerivedCategory.Plus (ModuleSheaf X R) :=
  (directImage f (ModuleCat.{u} R)).rightDerivedFunctorPlus

/-- A sheaf in degree zero followed by actual bounded-below derived direct image. -/
def derivedDirectImage : ModuleSheaf Z R ⥤ DerivedCategory.Plus (ModuleSheaf X R) :=
  Langlands.Cohomology.DerivedPlus.derivedComplex (directImage f (ModuleCat.{u} R))

/-- The actual integer-indexed bounded-below image of the chosen resolution. -/
def complex (F : ModuleSheaf Z R) : CochainComplex.Plus (ModuleSheaf X R) :=
  (directImage f (ModuleCat.{u} R)).mapCochainComplexPlus.obj
    (Langlands.Cohomology.DerivedPlus.resolutionPlus (injectiveResolution F))

/-- Every actual injective resolution on Z computes the derived image. -/
def resolutionIso {F : ModuleSheaf Z R} (I : InjectiveResolution F) :
    (derivedDirectImage f R).obj F ≅
      DerivedCategory.Plus.Q.obj
        ((directImage f (ModuleCat.{u} R)).mapCochainComplexPlus.obj
          (Langlands.Cohomology.DerivedPlus.resolutionPlus I)) :=
  Langlands.Cohomology.DerivedPlus.derivedComplexIso (directImage f (ModuleCat.{u} R)) I

def complexIso (F : ModuleSheaf Z R) :
    (derivedDirectImage f R).obj F ≅ DerivedCategory.Plus.Q.obj (complex f R F) :=
  resolutionIso f R (injectiveResolution F)

/-- The chosen lift of a coefficient map, followed termwise by direct image.
Functor laws are obtained after localization, as recorded below. -/
def complexMap {F G : ModuleSheaf Z R} (a : F ⟶ G) :
    complex f R F ⟶ complex f R G :=
  (directImage f (ModuleCat.{u} R)).mapCochainComplexPlus.map
    (Langlands.Cohomology.DerivedPlus.resolutionPlusMap
      (Langlands.Cohomology.DerivedPlus.descHom a (injectiveResolution F) (injectiveResolution G)))

@[reassoc] theorem resolutionIso_hom_naturality
    {F G : ModuleSheaf Z R} {a : F ⟶ G}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (t : InjectiveResolution.Hom I J a) :
    (derivedDirectImage f R).map a ≫ (resolutionIso f R J).hom =
      (resolutionIso f R I).hom ≫ DerivedCategory.Plus.Q.map
        ((directImage f (ModuleCat.{u} R)).mapCochainComplexPlus.map
          (Langlands.Cohomology.DerivedPlus.resolutionPlusMap t)) :=
  Langlands.Cohomology.DerivedPlus.derivedComplexIso_hom_naturality
    (directImage f (ModuleCat.{u} R)) t

@[reassoc] theorem complexIso_hom_naturality
    {F G : ModuleSheaf Z R} (a : F ⟶ G) :
    (derivedDirectImage f R).map a ≫ (complexIso f R G).hom =
      (complexIso f R F).hom ≫ DerivedCategory.Plus.Q.map (complexMap f R a) :=
  resolutionIso_hom_naturality f R
    (Langlands.Cohomology.DerivedPlus.descHom a (injectiveResolution F) (injectiveResolution G))

/-- Homology of the constructed derived object recovers higher direct image,
naturally in every coefficient map. -/
def homologyNatIso (q : ℕ) :
    derivedDirectImage f R ⋙ DerivedCategory.Plus.homologyFunctor (ModuleSheaf X R) q ≅
      higherDirectImage f R q :=
  Langlands.Cohomology.DerivedPlus.homologyNatIso (directImage f (ModuleCat.{u} R)) q

def homologyZeroIso :
    derivedDirectImage f R ⋙ DerivedCategory.Plus.homologyFunctor (ModuleSheaf X R) 0 ≅
      directImage f (ModuleCat.{u} R) :=
  homologyNatIso f R 0 ≪≫ higherDirectImageZeroIso f R

theorem isZero_homology_of_neg (F : ModuleSheaf Z R) {q : ℤ} (hq : q < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X R) q).obj
      ((derivedDirectImage f R).obj F)) :=
  Langlands.Cohomology.DerivedPlus.isZero_homology_of_neg
    (directImage f (ModuleCat.{u} R)) F hq

/-- Actual diagrams of coefficient sheaves give diagrams of derived images. -/
def diagramFunctor (K : Type uK) [Category.{vK} K] :
    (K ⥤ ModuleSheaf Z R) ⥤ (K ⥤ DerivedCategory.Plus (ModuleSheaf X R)) :=
  (Functor.whiskeringRight K _ _).obj (derivedDirectImage f R)

end DerivedPlus

end Langlands.Geometry.EtaleDerivedDirectImage

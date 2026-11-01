import Langlands.Geometry.EtaleTransportInduction
import Langlands.Geometry.EtaleTransportDerivedSections
import Langlands.Geometry.EtaleDerivedSectionsPlus
import Langlands.Cohomology.DerivedExactPostcomposition
import Langlands.Cohomology.DerivedPlusSource

/-! # Ordinary cohomology underlying actual derived transport sections -/

noncomputable section

universe u w wS wO wRep wMod uK vK

namespace Langlands.Geometry.EtaleTransport.DerivedComparison

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {Y : Scheme.{u}} {G : Type w} [Group G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ) [Small.{u} G]
variable (R : Type u) [CommRing R]

/-- Restriction carries an actual transport injective resolution to an ordinary one. -/
abbrev ordinaryResolution {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) :
    InjectiveResolution ((toSheaf ρ (ModuleCat.{u} R)).obj F) :=
  Langlands.Cohomology.DerivedComparison.mapInjectiveResolution
    (toSheaf ρ (ModuleCat.{u} R)) I

/-- The mapped augmentation in degree zero is the actual restricted augmentation. -/
theorem ordinaryResolution_ι_f_zero {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) :
    (ordinaryResolution ρ R I).ι.f 0 = (toSheaf ρ (ModuleCat.{u} R)).map (I.ι.f 0) :=
  Langlands.Cohomology.DerivedComparison.mapInjectiveResolution_ι_f_zero _ I

/-- On any resolution, forgetting section representations gives ordinary section complexes. -/
def resolutionComplexIso {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) :
    ((forget₂ (Rep.{u} R G) (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj
        ((sectionComplex ρ R (.up ℕ)).obj I.cocomplex) ≅
      ((EtaleDerivedSections.sections Y R).mapHomologicalComplex (.up ℕ)).obj
        (ordinaryResolution ρ R I).cocomplex :=
  Langlands.Cohomology.DerivedComparison.complexIso (sectionRepresentation ρ R)
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) (toSheaf ρ (ModuleCat.{u} R))
    (EtaleDerivedSections.sections Y R) (sectionRepresentationOrdinaryIso ρ R) I.cocomplex

/-- Every cohomology representation has the ordinary etale-cohomology module underneath. -/
def cohomologyForgetIso (q : ℕ) :
    DerivedSections.cohomology ρ R q ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ≅
      toSheaf ρ (ModuleCat.{u} R) ⋙ EtaleDerivedSections.cohomology Y R q :=
  Langlands.Cohomology.DerivedComparison.rightDerivedCompIso (sectionRepresentation ρ R)
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) (toSheaf ρ (ModuleCat.{u} R))
    (EtaleDerivedSections.sections Y R) (sectionRepresentationOrdinaryIso ρ R) q

section BoundedBelow

variable [HasDerivedCategory.{wS} (ModuleSheaf.{u, w, u, u} ρ R)]
  [HasDerivedCategory.{wO} (EtaleDerivedSections.ModuleSheaf Y R)]
  [HasDerivedCategory.{wRep} (Rep.{u} R G)]
  [HasDerivedCategory.{wMod} (ModuleCat.{u} R)]

/-- Derive the actual forgotten section functor in the transport-sheaf source category. -/
def moduleDerivedSections :
    ModuleSheaf.{u, w, u, u} ρ R ⥤ DerivedCategory.Plus (ModuleCat.{u} R) :=
  Langlands.Cohomology.DerivedPlus.derivedComplex
    (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))

omit [HasDerivedCategory (ModuleSheaf.{u, w, u, u} ρ R)]
  [HasDerivedCategory (EtaleDerivedSections.ModuleSheaf Y R)]
  [HasDerivedCategory (Rep.{u} R G)] [HasDerivedCategory (ModuleCat.{u} R)] in
private theorem resolutionSquare_isIso {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) :
    IsIso (Langlands.Cohomology.DerivedPlusSource.imageResolutionSquare
      (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
      (toSheaf ρ (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R)
      (sectionRepresentationOrdinaryIso ρ R).hom I) := by
  let τ := sectionRepresentationOrdinaryIso ρ R
  have : IsIso (Langlands.Cohomology.DerivedPlusSource.resolutionSquare
      (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
      (toSheaf ρ (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R) τ.hom I) :=
    inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex τ (.up ℕ)).app I.cocomplex).hom)
  have : IsIso ((CochainComplex.Plus.ι (ModuleCat.{u} R)).map
      (Langlands.Cohomology.DerivedPlusSource.imageResolutionSquare
        (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
        (toSheaf ρ (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R) τ.hom I)) :=
    inferInstanceAs (IsIso ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).map
      (Langlands.Cohomology.DerivedPlusSource.resolutionSquare
        (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
        (toSheaf ρ (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R) τ.hom I)))
  exact isIso_of_reflects_iso _ (CochainComplex.Plus.ι (ModuleCat.{u} R))

/-- The actual square on section functors induces the ordinary derived comparison map. -/
def ordinaryDerivedMap :
    moduleDerivedSections ρ R ⟶
      toSheaf ρ (ModuleCat.{u} R) ⋙ EtaleDerivedSectionsPlus.derivedSections Y R :=
  Langlands.Cohomology.DerivedPlusSource.derivedMap
      (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
      (toSheaf ρ (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R)
      (sectionRepresentationOrdinaryIso ρ R).hom

omit [HasDerivedCategory (Rep.{u} R G)] in
private theorem ordinaryDerivedMap_app_isIso (F : ModuleSheaf.{u, w, u, u} ρ R) :
    IsIso ((ordinaryDerivedMap ρ R).app F) := by
  unfold ordinaryDerivedMap
  rw [Langlands.Cohomology.DerivedPlusSource.derivedMap_app _ _ _ _ (injectiveResolution F)]
  unfold Langlands.Cohomology.DerivedPlusSource.derivedMapOfResolution
  have := resolutionSquare_isIso ρ R (injectiveResolution F)
  let e : (moduleDerivedSections ρ R).obj F ≅
      (toSheaf ρ (ModuleCat.{u} R) ⋙ EtaleDerivedSectionsPlus.derivedSections Y R).obj F :=
    Langlands.Cohomology.DerivedPlusSource.imageResolutionIso
        (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
        (injectiveResolution F) ≪≫
      DerivedCategory.Plus.Q.mapIso (asIso
        (Langlands.Cohomology.DerivedPlusSource.imageResolutionSquare
          (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
          (toSheaf ρ (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R)
          (sectionRepresentationOrdinaryIso ρ R).hom (injectiveResolution F))) ≪≫
      (Langlands.Cohomology.DerivedPlusSource.imageResolutionIso
        (EtaleDerivedSections.sections Y R)
        (ordinaryResolution ρ R (injectiveResolution F))).symm
  exact e.isIso_hom

/-- The derived forgotten sections are ordinary derived sections of the restricted sheaf. -/
def ordinaryDerivedIso :
    moduleDerivedSections ρ R ≅
      toSheaf ρ (ModuleCat.{u} R) ⋙ EtaleDerivedSectionsPlus.derivedSections Y R := by
  haveI : ∀ F, IsIso ((ordinaryDerivedMap ρ R).app F) :=
    ordinaryDerivedMap_app_isIso ρ R
  haveI : IsIso (ordinaryDerivedMap ρ R) := NatIso.isIso_of_isIso_app _
  exact asIso (ordinaryDerivedMap ρ R)

omit [HasDerivedCategory (Rep.{u} R G)] in
/-- Every transport resolution computes the ordinary derived comparison. -/
theorem ordinaryDerivedIso_hom_app {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) :
    (ordinaryDerivedIso ρ R).hom.app F =
      Langlands.Cohomology.DerivedPlusSource.derivedMapOfResolution
        (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
        (toSheaf ρ (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R)
        (sectionRepresentationOrdinaryIso ρ R).hom I :=
  Langlands.Cohomology.DerivedPlusSource.derivedMap_app _ _ _ _ I

omit [HasDerivedCategory (Rep.{u} R G)] in
/-- Cohomology of the comparison is the actual square on any restricted resolution. -/
theorem ordinaryDerivedIso_homology {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
        ((ordinaryDerivedIso ρ R).hom.app F) ≫
        (Langlands.Cohomology.DerivedPlus.homologyIso
          (EtaleDerivedSections.sections Y R) (ordinaryResolution ρ R I) q).hom =
      (Langlands.Cohomology.DerivedPlus.homologyIso
        (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) I q).hom ≫
        (I.isoRightDerivedObj
          (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) q).hom ≫
        HomologicalComplex.homologyMap
          (Langlands.Cohomology.DerivedPlusSource.resolutionSquare
            (sectionRepresentation ρ R ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
            (toSheaf ρ (ModuleCat.{u} R)) (EtaleDerivedSections.sections Y R)
            (sectionRepresentationOrdinaryIso ρ R).hom I) q ≫
        ((ordinaryResolution ρ R I).isoRightDerivedObj
          (EtaleDerivedSections.sections Y R) q).inv :=
  Langlands.Cohomology.DerivedPlusSource.derivedMap_homology _ _ _ _ I q

/-- Nonnegative homology of the derived module object is ordinary etale cohomology. -/
def moduleHomologyNatIso (q : ℕ) :
    moduleDerivedSections ρ R ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ≅
      toSheaf ρ (ModuleCat.{u} R) ⋙ EtaleDerivedSections.cohomology Y R q :=
  Functor.isoWhiskerRight (ordinaryDerivedIso ρ R) _ ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (toSheaf ρ (ModuleCat.{u} R))
        (EtaleDerivedSectionsPlus.homologyNatIso Y R q)

/-- Forgetting the actual derived representation agrees with ordinary derived sections,
after inclusion into the unbounded derived category of modules. -/
def derivedForgetIso :
    (DerivedSections.derivedSections ρ R ⋙ DerivedCategory.Plus.ι) ⋙
        (forget₂ (Rep.{u} R G) (ModuleCat.{u} R)).mapDerivedCategory ≅
      (toSheaf ρ (ModuleCat.{u} R) ⋙ EtaleDerivedSectionsPlus.derivedSections Y R) ⋙
        DerivedCategory.Plus.ι :=
  Langlands.Cohomology.DerivedPlus.derivedPostcompIso (sectionRepresentation ρ R)
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R)) ≪≫
      Functor.isoWhiskerRight (ordinaryDerivedIso ρ R) DerivedCategory.Plus.ι

/-- The ordinary derived comparison extends naturally to every coefficient diagram. -/
def diagramOrdinaryIso (K : Type uK) [Category.{vK} K]
    (D : K ⥤ ModuleSheaf.{u, w, u, u} ρ R) :
    D ⋙ moduleDerivedSections ρ R ≅
      D ⋙ (toSheaf ρ (ModuleCat.{u} R) ⋙ EtaleDerivedSectionsPlus.derivedSections Y R) :=
  Functor.isoWhiskerLeft D (ordinaryDerivedIso ρ R)

end BoundedBelow

end Langlands.Geometry.EtaleTransport.DerivedComparison

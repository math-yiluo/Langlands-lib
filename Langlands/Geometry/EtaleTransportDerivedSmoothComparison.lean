import Langlands.Geometry.EtaleTransportDerivedSmoothSections
import Langlands.Geometry.EtaleTransportDerivedComparison
import Langlands.Cohomology.HyperextScalarExtension
import Langlands.Cohomology.DerivedPlusSourceFunctoriality

/-! # Derived smooth sections and their natural algebraic comparison -/

noncomputable section

universe u w wS wSm wRep wO wMod uK vK

namespace Langlands.Geometry.EtaleTransport.DerivedSmoothComparison

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {Y : Scheme.{u}} {G : Type w} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
variable (ρ : G →* (Aut Y)ᵐᵒᵖ) [Small.{u} G]
variable (R : Type u) [CommRing R]

local instance : PreservesFiniteColimits
    (SmoothRep.toRep : SmoothRep.{u, w, u} R G ⥤ Rep.{u} R G) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Forgetting smoothness commutes with classical right-derived smooth sections. -/
def cohomologyForgetIso (q : ℕ) :
    DerivedSmoothSections.cohomology ρ R q ⋙ SmoothRep.toRep ≅
      (SmoothSections.sections ρ R ⋙ SmoothRep.toRep).rightDerived q :=
  Langlands.Cohomology.DerivedComparison.rightDerivedCompIso (SmoothSections.sections ρ R)
      (SmoothRep.toRep : SmoothRep.{u, w, u} R G ⥤ Rep.{u} R G)
      (𝟭 (ModuleSheaf.{u, w, u, u} ρ R))
      (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
      (Functor.leftUnitor _).symm q ≪≫ Functor.leftUnitor _

/-- The derived section inclusion gives a natural map to algebraic section cohomology. -/
def cohomologyMap (q : ℕ) :
    DerivedSmoothSections.cohomology ρ R q ⋙ SmoothRep.toRep ⟶
      DerivedSections.cohomology ρ R q :=
  (cohomologyForgetIso ρ R q).hom ≫ NatTrans.rightDerived (SmoothSections.inclusion ρ R) q

/-- Every transport-sheaf injective resolution computes the classical comparison. -/
theorem cohomologyMap_app {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) (q : ℕ) :
    (cohomologyMap ρ R q).app F =
      (cohomologyForgetIso ρ R q).hom.app F ≫
        (I.isoRightDerivedObj (SmoothSections.sections ρ R ⋙ SmoothRep.toRep) q).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (SmoothSections.inclusion ρ R) (.up ℕ)).app
            I.cocomplex) q ≫
        (I.isoRightDerivedObj (sectionRepresentation ρ R) q).inv := by
  change (cohomologyForgetIso ρ R q).hom.app F ≫
    (NatTrans.rightDerived (SmoothSections.inclusion ρ R) q).app F = _
  rw [InjectiveResolution.rightDerived_app_eq (SmoothSections.inclusion ρ R) I q]
  rfl

section BoundedBelow

variable [HasDerivedCategory.{wS} (ModuleSheaf.{u, w, u, u} ρ R)]
  [HasDerivedCategory.{wSm} (SmoothRep.{u, w, u} R G)]
  [HasDerivedCategory.{wRep} (Rep.{u} R G)]

/-- Derive the underlying algebraic representation of smooth sections in the sheaf source. -/
def algebraicSmoothDerivedSections :
    ModuleSheaf.{u, w, u, u} ρ R ⥤ DerivedCategory.Plus (Rep.{u} R G) :=
  Langlands.Cohomology.DerivedPlus.derivedComplex (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)

/-- Exact forgetting of smoothness commutes with the actual derived section object. -/
def derivedForgetIso :
    (DerivedSmoothSections.derivedSections ρ R ⋙ DerivedCategory.Plus.ι) ⋙
        SmoothRep.toRep.mapDerivedCategory ≅
      algebraicSmoothDerivedSections ρ R ⋙ DerivedCategory.Plus.ι :=
  Langlands.Cohomology.DerivedPlus.derivedPostcompIso (SmoothSections.sections ρ R)
    (SmoothRep.toRep : SmoothRep.{u, w, u} R G ⥤ Rep.{u} R G)

/-- The smooth-section counit, as a square over the identity source functor. -/
def inclusionSquare :
    SmoothSections.sections ρ R ⋙ SmoothRep.toRep ⟶
      𝟭 (ModuleSheaf.{u, w, u, u} ρ R) ⋙ sectionRepresentation ρ R :=
  SmoothSections.inclusion ρ R ≫ (Functor.leftUnitor _).inv

/-- The actual smooth-section inclusion induces a bounded-below derived comparison. -/
def algebraicDerivedMap :
    algebraicSmoothDerivedSections ρ R ⟶ DerivedSections.derivedSections ρ R :=
  Langlands.Cohomology.DerivedPlusSource.derivedMap
      (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
      (𝟭 (ModuleSheaf.{u, w, u, u} ρ R)) (sectionRepresentation ρ R)
      (inclusionSquare ρ R) ≫ (Functor.leftUnitor _).hom

omit [HasDerivedCategory (SmoothRep.{u, w, u} R G)] in
/-- Every injective resolution computes the bounded-below comparison component. -/
theorem algebraicDerivedMap_app {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) :
    (algebraicDerivedMap ρ R).app F =
      Langlands.Cohomology.DerivedPlusSource.derivedMapOfResolution
        (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
        (𝟭 (ModuleSheaf.{u, w, u, u} ρ R)) (sectionRepresentation ρ R)
        (inclusionSquare ρ R) I := by
  change (Langlands.Cohomology.DerivedPlusSource.derivedMap
      (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
      (𝟭 (ModuleSheaf.{u, w, u, u} ρ R)) (sectionRepresentation ρ R)
      (inclusionSquare ρ R)).app F ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact Langlands.Cohomology.DerivedPlusSource.derivedMap_app
    (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
    (𝟭 (ModuleSheaf.{u, w, u, u} ρ R)) (sectionRepresentation ρ R)
    (inclusionSquare ρ R) I

omit [HasDerivedCategory (SmoothRep.{u, w, u} R G)] in
/-- Cohomology of the comparison is induced by the actual resolution square. -/
theorem algebraicDerivedMap_homology {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) q).map
        ((algebraicDerivedMap ρ R).app F) ≫
        (Langlands.Cohomology.DerivedPlus.homologyIso (sectionRepresentation ρ R)
          (Langlands.Cohomology.DerivedComparison.mapInjectiveResolution (𝟭 _) I) q).hom =
      (Langlands.Cohomology.DerivedPlus.homologyIso
        (SmoothSections.sections ρ R ⋙ SmoothRep.toRep) I q).hom ≫
        (I.isoRightDerivedObj (SmoothSections.sections ρ R ⋙ SmoothRep.toRep) q).hom ≫
        HomologicalComplex.homologyMap
          (Langlands.Cohomology.DerivedPlusSource.resolutionSquare
            (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
            (𝟭 (ModuleSheaf.{u, w, u, u} ρ R)) (sectionRepresentation ρ R)
            (inclusionSquare ρ R) I) q ≫
        ((Langlands.Cohomology.DerivedComparison.mapInjectiveResolution (𝟭 _) I).isoRightDerivedObj (sectionRepresentation ρ R) q).inv := by
  change (DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) q).map
      ((Langlands.Cohomology.DerivedPlusSource.derivedMap
        (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
        (𝟭 (ModuleSheaf.{u, w, u, u} ρ R)) (sectionRepresentation ρ R)
        (inclusionSquare ρ R)).app F ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  exact Langlands.Cohomology.DerivedPlusSource.derivedMap_homology
    (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
    (𝟭 (ModuleSheaf.{u, w, u, u} ρ R)) (sectionRepresentation ρ R)
    (inclusionSquare ρ R) I q

omit [HasDerivedCategory (ModuleSheaf.{u, w, u, u} ρ R)]
  [HasDerivedCategory (SmoothRep.{u, w, u} R G)]
  [HasDerivedCategory (Rep.{u} R G)] in
private def idResolutionHom {F : ModuleSheaf.{u, w, u, u} ρ R}
    (I : InjectiveResolution F) :
    InjectiveResolution.Hom
      (Langlands.Cohomology.DerivedComparison.mapInjectiveResolution (𝟭 _) I) I (𝟙 F) where
  hom := (Functor.mapHomologicalComplexIdIso _ (.up ℕ)).hom.app I.cocomplex
  ι_f_zero_comp_hom_f_zero := by
    rw [Langlands.Cohomology.DerivedComparison.mapInjectiveResolution_ι_f_zero]
    change I.ι.f 0 ≫ 𝟙 _ = _ ≫ I.ι.f 0
    rw [CochainComplex.single₀_map_f_zero]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

omit [HasDerivedCategory (SmoothRep.{u, w, u} R G)] in
set_option backward.isDefEq.respectTransparency false in
/-- The bounded-below comparison induces the classical derived inclusion. -/
theorem algebraicDerivedMap_homology_classical
    {F : ModuleSheaf.{u, w, u, u} ρ R} (I : InjectiveResolution F) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) q).map
        ((algebraicDerivedMap ρ R).app F) ≫
        (DerivedSections.homologyNatIso ρ R q).hom.app F =
      (Langlands.Cohomology.DerivedPlus.homologyNatIso
        (SmoothSections.sections ρ R ⋙ SmoothRep.toRep) q).hom.app F ≫
        (NatTrans.rightDerived (SmoothSections.inclusion ρ R) q).app F := by
  let J : InjectiveResolution F :=
    Langlands.Cohomology.DerivedComparison.mapInjectiveResolution (𝟭 _) I
  let φ := idResolutionHom ρ R I
  have hc : J.ι.f 0 ≫ φ.hom.f 0 = (𝟙 F) ≫ I.ι.f 0 :=
    φ.ι_f_zero_comp_hom_f_zero.trans (by rw [CochainComplex.single₀_map_f_zero])
  have ht := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (𝟙 F) J I φ.hom hc (sectionRepresentation ρ R) q
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at ht
  have hs :
      Langlands.Cohomology.DerivedPlusSource.resolutionSquare
          (SmoothSections.sections ρ R ⋙ SmoothRep.toRep)
          (𝟭 (ModuleSheaf.{u, w, u, u} ρ R)) (sectionRepresentation ρ R)
          (inclusionSquare ρ R) I ≫
          ((sectionRepresentation ρ R).mapHomologicalComplex (.up ℕ)).map φ.hom =
        (NatTrans.mapHomologicalComplex (SmoothSections.inclusion ρ R) (.up ℕ)).app
          I.cocomplex := by
    ext n : 1
    change ((SmoothSections.inclusion ρ R).app (I.cocomplex.X n) ≫ 𝟙 _) ≫
      (sectionRepresentation ρ R).map (𝟙 _) = _
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  erw [Langlands.Cohomology.DerivedPlus.homologyNatIso_hom_app
      (sectionRepresentation ρ R) q J,
    algebraicDerivedMap_homology ρ R I q,
    Langlands.Cohomology.DerivedPlus.homologyNatIso_hom_app
      (SmoothSections.sections ρ R ⋙ SmoothRep.toRep) q I,
    InjectiveResolution.rightDerived_app_eq (SmoothSections.inclusion ρ R) I q]
  rw [ht]
  dsimp only [Functor.comp_map]
  erw [← HomologicalComplex.homologyMap_comp_assoc, hs]
  rfl

/-- Cohomology of the algebraic model is forgotten smooth cohomology. -/
def algebraicHomologyNatIso (q : ℕ) :
    algebraicSmoothDerivedSections ρ R ⋙
        DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) q ≅
      DerivedSmoothSections.cohomology ρ R q ⋙ SmoothRep.toRep :=
  Langlands.Cohomology.DerivedPlus.homologyNatIso
      (SmoothSections.sections ρ R ⋙ SmoothRep.toRep) q ≪≫
    (cohomologyForgetIso ρ R q).symm

omit [HasDerivedCategory (SmoothRep.{u, w, u} R G)] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual derived comparison and the classical comparison agree on cohomology. -/
theorem algebraicDerivedMap_homologyMap
    (F : ModuleSheaf.{u, w, u, u} ρ R) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (Rep.{u} R G) q).map
        ((algebraicDerivedMap ρ R).app F) ≫
        (DerivedSections.homologyNatIso ρ R q).hom.app F =
      (algebraicHomologyNatIso ρ R q).hom.app F ≫ (cohomologyMap ρ R q).app F := by
  rw [algebraicDerivedMap_homology_classical ρ R (injectiveResolution F) q]
  simp only [algebraicHomologyNatIso, cohomologyMap, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Forget the genuine derived smooth object and compare it naturally to algebraic sections. -/
def derivedMap :
    (DerivedSmoothSections.derivedSections ρ R ⋙ DerivedCategory.Plus.ι) ⋙
        SmoothRep.toRep.mapDerivedCategory ⟶
      DerivedSections.derivedSections ρ R ⋙ DerivedCategory.Plus.ι :=
  (derivedForgetIso ρ R).hom ≫
    Functor.whiskerRight (algebraicDerivedMap ρ R) DerivedCategory.Plus.ι

/-- The comparison extends to arbitrary coefficient diagrams by postcomposition. -/
def diagramDerivedMap (K : Type uK) [Category.{vK} K]
    (D : K ⥤ ModuleSheaf.{u, w, u, u} ρ R) :
    D ⋙ ((DerivedSmoothSections.derivedSections ρ R ⋙ DerivedCategory.Plus.ι) ⋙
        SmoothRep.toRep.mapDerivedCategory) ⟶
      D ⋙ (DerivedSections.derivedSections ρ R ⋙ DerivedCategory.Plus.ι) :=
  Functor.whiskerLeft D (derivedMap ρ R)

end BoundedBelow

end Langlands.Geometry.EtaleTransport.DerivedSmoothComparison

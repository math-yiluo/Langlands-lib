import Langlands.Geometry.EtaleDerivedGlobalCoherence

/-! # Singleton and cohomology coherence for actual geometric pullback -/

noncomputable section

universe u wX wZ wV wR

namespace Langlands.Geometry.EtaleDerivedInverseImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]

/-- On every actual singleton, the derived identity comparison is the ordinary
geometric identity transported through the existing singleton comparison. -/
@[reassoc] theorem functorId_hom_app_single (n : ℤ) (F : ModuleSheaf X R) :
    (functorId R X).hom.app ((DerivedCategory.singleFunctor (ModuleSheaf X R) n).obj F) =
      (singleIso (𝟙 X) R n).hom.app F ≫
        (DerivedCategory.singleFunctor (ModuleSheaf X R) n).map
          ((inverseImageId R X).hom.app F) := by
  dsimp only [singleIso]
  have hi := (singleMapHomologicalComplex (𝟭 (ModuleSheaf X R)) (.up ℤ) n).hom.naturality
    ((inverseImageId R X).hom.app F)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hi
  simp [← DerivedCategory.Q_obj_single_obj, functorId_hom_app_Q, factors,
    NatIso.mapHomologicalComplex, ← DerivedCategory.Q_map_single_map,
    CochainComplex.singleFunctor,
    Functor.mapDerivedCategorySingleFunctor_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app,
    natTransMapHomologicalComplex_app_single_obj,
    ← singleMapHomologicalComplex_id_hom_app, ← Functor.map_comp]
  rw [hi]
  simp

/-- The same actual singleton identity in the bounded-below derived category. -/
@[reassoc] theorem plusFunctorId_hom_app_single (n : ℤ) (F : ModuleSheaf X R) :
    (plusFunctorId R X).hom.app
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) n).obj F) =
      (plusSingleIso (𝟙 X) R n).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) n).map
          ((inverseImageId R X).hom.app F) := by
  apply (DerivedCategory.Plus.ι (C := ModuleSheaf X R)).map_injective
  simp only [plusFunctorId, plusSingleIso, NatIso.ofComponents_hom_app,
    Iso.app_hom, Functor.preimageIso_hom, Functor.map_preimage, Functor.map_comp]
  exact functorId_hom_app_single R n F

variable [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wV} (ModuleSheaf V R)]

set_option maxHeartbeats 1200000 in
/-- Singleton compatibility of actual derived geometric composition. -/
@[reassoc] theorem functorComp_hom_app_single (f : Z ⟶ X) (g : V ⟶ Z)
    (n : ℤ) (F : ModuleSheaf X R) :
    (functorComp R f g).hom.app
        ((DerivedCategory.singleFunctor (ModuleSheaf X R) n).obj F) ≫
      (singleIso (g ≫ f) R n).hom.app F =
    (functor g R).map ((singleIso f R n).hom.app F) ≫
      (singleIso g R n).hom.app ((inverseImage f R).obj F) ≫
      (DerivedCategory.singleFunctor (ModuleSheaf V R) n).map
        ((inverseImageComp R f g).hom.app F) := by
  dsimp only [singleIso]
  simp only [← DerivedCategory.Q_obj_single_obj, functorComp_hom_app_Q,
    Functor.mapDerivedCategorySingleFunctor_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app, Category.comp_id,
    Functor.map_comp, Category.assoc]
  dsimp only [functor, factors, CochainComplex.singleFunctor,
    Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex]
  simp only [DerivedCategory.Q_obj_single_obj, Functor.comp_obj,
    natTransMapHomologicalComplex_app_single_obj,
    singleMapHomologicalComplex_comp_hom_app, Category.assoc,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id,
    ← DerivedCategory.Q_map_single_map]
  simp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_inv, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  have hn := (inverseImage g R).mapDerivedCategoryFactors.hom.naturality
    ((singleMapHomologicalComplex (inverseImage f R) (.up ℤ) n).hom.app F)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, Functor.map_comp]
  erw [DerivedCategory.Q.map_id]
  simp only [Category.id_comp, Functor.map_comp]

/-- The same singleton composition in the bounded-below derived category. -/
@[reassoc] theorem plusFunctorComp_hom_app_single (f : Z ⟶ X) (g : V ⟶ Z)
    (n : ℤ) (F : ModuleSheaf X R) :
    (plusFunctorComp R f g).hom.app
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) n).obj F) ≫
      (plusSingleIso (g ≫ f) R n).hom.app F =
    (plusFunctor g R).map ((plusSingleIso f R n).hom.app F) ≫
      (plusSingleIso g R n).hom.app ((inverseImage f R).obj F) ≫
      (DerivedCategory.Plus.singleFunctor (ModuleSheaf V R) n).map
        ((inverseImageComp R f g).hom.app F) := by
  apply (DerivedCategory.Plus.ι (C := ModuleSheaf V R)).map_injective
  simp only [plusFunctorComp, plusSingleIso, NatIso.ofComponents_hom_app,
    Iso.app_hom, Functor.preimageIso_hom, Functor.map_preimage, Functor.map_comp]
  change (functorComp R f g).hom.app
      ((DerivedCategory.singleFunctor (ModuleSheaf X R) n).obj F) ≫
      (singleIso (g ≫ f) R n).hom.app F =
    (functor g R).map ((DerivedCategory.Plus.ι (C := ModuleSheaf Z R)).map
      ((plusSingleIso f R n).hom.app F)) ≫
      (singleIso g R n).hom.app ((inverseImage f R).obj F) ≫
      (DerivedCategory.singleFunctor (ModuleSheaf V R) n).map
        ((inverseImageComp R f g).hom.app F)
  simp only [plusSingleIso, NatIso.ofComponents_hom_app, Iso.app_hom,
    Functor.preimageIso_hom, Functor.map_preimage]
  exact functorComp_hom_app_single R f g n F

end Langlands.Geometry.EtaleDerivedInverseImage

namespace Langlands.Geometry.EtaleDerivedGlobalPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections EtaleDerivedInverseImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z V : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (ModuleSheaf X R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Identity on derived sections of every actual coefficient sheaf. -/
@[reassoc] theorem sheafDerivedPullback_id (F : ModuleSheaf X R) :
    (sheafDerivedPullback (𝟙 X) R).app F ≫
      (EtaleDerivedSectionsPlus.derivedSections X R).map
        ((inverseImageId R X).hom.app F) = 𝟙 _ := by
  simp only [sheafDerivedPullback, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  change (derivedPullback (𝟙 X) R).app
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) 0).obj F) ≫
      (EtaleDerivedSectionsPlus.rightDerivedFunctor X R).map
        ((plusSingleIso (𝟙 X) R 0).hom.app F) ≫
      (EtaleDerivedSectionsPlus.rightDerivedFunctor X R).map
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) 0).map
          ((inverseImageId R X).hom.app F)) = 𝟙 _
  rw [← Functor.map_comp, ← plusFunctorId_hom_app_single, derivedPullback_id]

/-- Identity for ordinary small-etale cohomology in every nonnegative degree. -/
@[reassoc] theorem cohomologyPullback_id (q : ℕ) (F : ModuleSheaf X R) :
    (cohomologyPullback (𝟙 X) R q).app F ≫
      (cohomology X R q).map ((inverseImageId R X).hom.app F) = 𝟙 _ := by
  have hn := (EtaleDerivedSectionsPlus.homologyNatIso X R q).hom.naturality
    ((inverseImageId R X).hom.app F)
  dsimp only [Functor.comp_map] at hn
  simp only [cohomologyPullback, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
    Category.assoc]
  rw [← hn, ← Functor.map_comp_assoc, sheafDerivedPullback_id,
    CategoryTheory.Functor.map_id,
    Category.id_comp]
  dsimp only [Functor.id_obj]
  exact Iso.inv_hom_id_app _ _

variable [HasDerivedCategory.{wZ} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wV} (ModuleSheaf V R)]

/-- Successive pullback on derived sections of actual coefficient sheaves. -/
def compositeSheafDerivedPullback (f : Z ⟶ X) (g : V ⟶ Z) :
    EtaleDerivedSectionsPlus.derivedSections X R ⟶
      (inverseImage f R ⋙ inverseImage g R) ⋙
        EtaleDerivedSectionsPlus.derivedSections V R :=
  sheafDerivedPullback f R ≫
    Functor.whiskerLeft (inverseImage f R) (sheafDerivedPullback g R) ≫
    (Functor.associator _ _ _).inv

/-- Composition on derived sections of every actual coefficient sheaf, with
its constructed ordinary geometric coefficient comparison. -/
@[reassoc] theorem sheafDerivedPullback_comp (f : Z ⟶ X) (g : V ⟶ Z)
    (F : ModuleSheaf X R) :
    (sheafDerivedPullback f R).app F ≫
      (sheafDerivedPullback g R).app ((inverseImage f R).obj F) ≫
      (EtaleDerivedSectionsPlus.derivedSections V R).map
        ((inverseImageComp R f g).hom.app F) =
    (sheafDerivedPullback (g ≫ f) R).app F := by
  have hn := (derivedPullback g R).naturality ((plusSingleIso f R 0).hom.app F)
  dsimp only [Functor.comp_map] at hn
  simp only [sheafDerivedPullback, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Category.assoc]
  change (derivedPullback f R).app
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) 0).obj F) ≫
      (EtaleDerivedSectionsPlus.rightDerivedFunctor Z R).map
        ((plusSingleIso f R 0).hom.app F) ≫
      (derivedPullback g R).app
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf Z R) 0).obj
          ((inverseImage f R).obj F)) ≫
      (EtaleDerivedSectionsPlus.rightDerivedFunctor V R).map
        ((plusSingleIso g R 0).hom.app ((inverseImage f R).obj F)) ≫
      (EtaleDerivedSectionsPlus.rightDerivedFunctor V R).map
        ((DerivedCategory.Plus.singleFunctor (ModuleSheaf V R) 0).map
          ((inverseImageComp R f g).hom.app F)) =
    (derivedPullback (g ≫ f) R).app
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf X R) 0).obj F) ≫
      (EtaleDerivedSectionsPlus.rightDerivedFunctor V R).map
        ((plusSingleIso (g ≫ f) R 0).hom.app F)
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, ← Functor.map_comp, Category.assoc,
    ← plusFunctorComp_hom_app_single, Functor.map_comp, derivedPullback_comp_assoc]

/-- The successive sheaf-derived transformation agrees with pullback along
the composite after the actual geometric coefficient identification. -/
theorem compositeSheafDerivedPullback_eq (f : Z ⟶ X) (g : V ⟶ Z) :
    compositeSheafDerivedPullback R f g ≫
      Functor.whiskerRight (inverseImageComp R f g).hom
        (EtaleDerivedSectionsPlus.derivedSections V R) =
    sheafDerivedPullback (g ≫ f) R := by
  apply NatTrans.ext
  funext F
  simpa [compositeSheafDerivedPullback] using sheafDerivedPullback_comp R f g F

/-- Successive ordinary small-etale cohomology pullback, natural in the sheaf. -/
def compositeCohomologyPullback (f : Z ⟶ X) (g : V ⟶ Z) (q : ℕ) :
    cohomology X R q ⟶ (inverseImage f R ⋙ inverseImage g R) ⋙ cohomology V R q :=
  cohomologyPullback f R q ≫
    Functor.whiskerLeft (inverseImage f R) (cohomologyPullback g R q) ≫
    (Functor.associator _ _ _).inv

/-- Composition for ordinary small-etale cohomology in every nonnegative degree. -/
@[reassoc] theorem cohomologyPullback_comp (f : Z ⟶ X) (g : V ⟶ Z)
    (q : ℕ) (F : ModuleSheaf X R) :
    (cohomologyPullback f R q).app F ≫
      (cohomologyPullback g R q).app ((inverseImage f R).obj F) ≫
      (cohomology V R q).map ((inverseImageComp R f g).hom.app F) =
    (cohomologyPullback (g ≫ f) R q).app F := by
  have hn := (EtaleDerivedSectionsPlus.homologyNatIso V R q).hom.naturality
    ((inverseImageComp R f g).hom.app F)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [cohomologyPullback, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc, sheafDerivedPullback_comp]

/-- Equality of the natural successive cohomology transformation and the
existing pullback along the composite, through its actual coefficient map. -/
theorem compositeCohomologyPullback_eq (f : Z ⟶ X) (g : V ⟶ Z) (q : ℕ) :
    compositeCohomologyPullback R f g q ≫
      Functor.whiskerRight (inverseImageComp R f g).hom (cohomology V R q) =
    cohomologyPullback (g ≫ f) R q := by
  apply NatTrans.ext
  funext F
  simpa [compositeCohomologyPullback] using cohomologyPullback_comp R f g q F

end Langlands.Geometry.EtaleDerivedGlobalPullback

import Langlands.Geometry.EtaleDerivedPlusPullbackFunctoriality

/-! # Geometric pullback of whole derived coefficient systems -/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry

universe u v w wX wY wZ wT

section Recovery

variable (X : Scheme.{u}) (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]
variable {J : Type v} [Category.{w} J]

/-- Canonical ordinary-cohomology recovery for every arrow of a coefficient
system on one scheme. -/
def systemDerivedSectionsHomologyIso
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) (q : ℕ) :
    (D ⋙ EtaleDerivedSectionsPlus.derivedSections X R) ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ≅
      D ⋙ EtaleDerivedSections.cohomology X R q :=
  Functor.associator D (EtaleDerivedSectionsPlus.derivedSections X R)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≪≫
    Functor.isoWhiskerLeft D (EtaleDerivedSectionsPlus.homologyNatIso X R q)

/-- Canonical degree-zero recovery of the whole ordinary-section system. -/
def systemDerivedSectionsZeroIso
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    (D ⋙ EtaleDerivedSectionsPlus.derivedSections X R) ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0 ≅
      D ⋙ EtaleDerivedSections.sections X R :=
  Functor.associator D (EtaleDerivedSectionsPlus.derivedSections X R)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≪≫
    Functor.isoWhiskerLeft D (EtaleDerivedSectionsPlus.homologyZeroIso X R)

end Recovery

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{wY} (EtaleDerivedSections.ModuleSheaf Y R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]
variable {J : Type v} [Category.{w} J]

/-- Actual geometric pullback, natural along the whole coefficient system.
The target consists of the restricted sheaves with their restricted maps. -/
def systemDerivedSectionsMap
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    D ⋙ EtaleDerivedSectionsPlus.derivedSections X R ⟶
      (D ⋙ restriction f (ModuleCat.{u} R)) ⋙
        EtaleDerivedSectionsPlus.derivedSections Y R :=
  Functor.whiskerLeft D (derivedSectionsMap f R)

/-- Pullback is natural in every morphism of whole coefficient systems. -/
def systemDerivedSectionsMapFunctor :
    EtaleDerivedSectionsPlus.diagramFunctor X R J ⟶
      (Functor.whiskeringRight J (EtaleDerivedSections.ModuleSheaf X R)
        (DerivedCategory.Plus (ModuleCat.{u} R))).obj
          (restriction f (ModuleCat.{u} R) ⋙
            EtaleDerivedSectionsPlus.derivedSections Y R) :=
  (Functor.whiskeringRight J (EtaleDerivedSections.ModuleSheaf X R)
    (DerivedCategory.Plus (ModuleCat.{u} R))).map (derivedSectionsMap f R)

@[simp]
theorem systemDerivedSectionsMapFunctor_app
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    (systemDerivedSectionsMapFunctor (J := J) f R).app D =
      systemDerivedSectionsMap f R D := rfl

@[simp]
theorem systemDerivedSectionsMap_app
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) (j : J) :
    (systemDerivedSectionsMap f R D).app j =
      (derivedSectionsMap f R).app (D.obj j) := rfl

/-- Every original coefficient transition commutes with geometric pullback. -/
@[reassoc]
theorem systemDerivedSectionsMap_naturality
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) {i j : J} (a : i ⟶ j) :
    (EtaleDerivedSectionsPlus.derivedSections X R).map (D.map a) ≫
        (systemDerivedSectionsMap f R D).app j =
      (systemDerivedSectionsMap f R D).app i ≫
        (EtaleDerivedSectionsPlus.derivedSections Y R).map
          ((restriction f (ModuleCat.{u} R)).map (D.map a)) :=
  (systemDerivedSectionsMap f R D).naturality a

/-- Geometric pullback of ordinary cohomology, retaining all coefficient maps. -/
def systemCohomologyMap
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) (q : ℕ) :
    D ⋙ EtaleDerivedSections.cohomology X R q ⟶
      (D ⋙ restriction f (ModuleCat.{u} R)) ⋙
        EtaleDerivedSections.cohomology Y R q :=
  Functor.whiskerLeft D (cohomologyMap f R q)

/-- Geometric restriction of ordinary sections of the whole system. -/
def systemSectionsMap
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    D ⋙ EtaleDerivedSections.sections X R ⟶
      (D ⋙ restriction f (ModuleCat.{u} R)) ⋙
        EtaleDerivedSections.sections Y R :=
  Functor.whiskerLeft D (sectionsMap f R)

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparisons recover the whole ordinary-cohomology pullback
from the actual derived natural transformation. -/
theorem systemDerivedSectionsMap_homology
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) (q : ℕ) :
    Functor.whiskerRight (systemDerivedSectionsMap f R D)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≫
        (systemDerivedSectionsHomologyIso Y R
          (D ⋙ restriction f (ModuleCat.{u} R)) q).hom =
      (systemDerivedSectionsHomologyIso X R D q).hom ≫
        systemCohomologyMap f R D q := by
  apply NatTrans.ext
  funext j
  simpa only [systemDerivedSectionsHomologyIso, systemDerivedSectionsMap,
    systemCohomologyMap, Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp]
    using derivedSectionsMap_homology f R (D.obj j) q

set_option backward.isDefEq.respectTransparency false in
/-- The same square in degree zero recovers actual ordinary sections. -/
theorem systemDerivedSectionsMap_zero
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    Functor.whiskerRight (systemDerivedSectionsMap f R D)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≫
        (systemDerivedSectionsZeroIso Y R
          (D ⋙ restriction f (ModuleCat.{u} R))).hom =
      (systemDerivedSectionsZeroIso X R D).hom ≫ systemSectionsMap f R D := by
  apply NatTrans.ext
  funext j
  simpa only [systemDerivedSectionsZeroIso, systemDerivedSectionsMap,
    systemSectionsMap, Functor.comp_obj, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp]
    using derivedSectionsMap_zero f R (D.obj j)

/-- Whole-system pullback along the identity is the identity after the actual
identity-restriction coefficient comparison. -/
theorem systemDerivedSectionsMap_id
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    systemDerivedSectionsMap (𝟙 X) R D ≫
        Functor.whiskerRight
          (Functor.whiskerLeft D (restrictionId (ModuleCat.{u} R)).hom)
          (EtaleDerivedSectionsPlus.derivedSections X R) = 𝟙 _ := by
  apply NatTrans.ext
  funext j
  exact derivedSectionsMap_id R (D.obj j)

variable {Z : Scheme.{u}}
variable [HasDerivedCategory.{wZ} (EtaleDerivedSections.ModuleSheaf Z R)]

/-- Whole-system geometric pullbacks compose after the canonical comparison
between successive restrictions and restriction along the composite. -/
theorem systemDerivedSectionsMap_comp (g : Z ⟶ Y) [Etale g]
    (D : J ⥤ EtaleDerivedSections.ModuleSheaf X R) :
    systemDerivedSectionsMap f R D ≫
        systemDerivedSectionsMap g R (D ⋙ restriction f (ModuleCat.{u} R)) ≫
        Functor.whiskerRight
          (Functor.whiskerLeft D (restrictionComp f (ModuleCat.{u} R) g).hom)
          (EtaleDerivedSectionsPlus.derivedSections Z R) =
      systemDerivedSectionsMap (g ≫ f) R D := by
  apply NatTrans.ext
  funext j
  exact derivedSectionsMap_comp f R g (D.obj j)

end Langlands.Geometry.EtalePullback

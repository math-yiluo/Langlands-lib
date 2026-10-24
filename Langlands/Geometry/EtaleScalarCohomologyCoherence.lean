import Langlands.Geometry.EtaleScalarCohomologyZero
import Langlands.Geometry.EtaleScalarDiagramSectionsCoherence

/-!
# Scalar coherence on etale cohomology
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable (φ : R →+* A) (ψ : A →+* B) (X : Scheme.{u})

/-- Apply cohomology over the fixed ring to the coefficient identity comparison. -/
def sheafScalarCohomologyIdIso (q : ℕ) :
    sheafRestrictScalars (RingHom.id R) X ⋙ EtaleDerivedSections.cohomology X R q ≅
      EtaleDerivedSections.cohomology X R q :=
  Functor.isoWhiskerRight (sheafRestrictScalarsIdIso X)
      (EtaleDerivedSections.cohomology X R q) ≪≫
    Functor.leftUnitor (EtaleDerivedSections.cohomology X R q)

/-- Split coefficient restriction before applying cohomology over the final ring. -/
def sheafScalarCohomologyCompIso (q : ℕ) :
    sheafRestrictScalars (ψ.comp φ) X ⋙ EtaleDerivedSections.cohomology X R q ≅
      sheafRestrictScalars ψ X ⋙ sheafRestrictScalars φ X ⋙
        EtaleDerivedSections.cohomology X R q :=
  Functor.isoWhiskerRight (sheafRestrictScalarsCompIso φ ψ X)
      (EtaleDerivedSections.cohomology X R q) ≪≫
    Functor.associator (sheafRestrictScalars ψ X) (sheafRestrictScalars φ X)
      (EtaleDerivedSections.cohomology X R q)

/-- The identity comparison acts by the usual cohomology map. -/
@[simp] theorem sheafScalarCohomologyIdIso_hom_app
    (q : ℕ) (F : EtaleDerivedSections.ModuleSheaf X R) :
    (sheafScalarCohomologyIdIso X q).hom.app F =
      (EtaleDerivedSections.cohomology X R q).map
        ((sheafRestrictScalarsIdIso X).hom.app F) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The composition comparison acts by the usual cohomology map. -/
@[simp] theorem sheafScalarCohomologyCompIso_hom_app
    (q : ℕ) (F : EtaleDerivedSections.ModuleSheaf X B) :
    (sheafScalarCohomologyCompIso φ ψ X q).hom.app F =
      (EtaleDerivedSections.cohomology X R q).map
        ((sheafRestrictScalarsCompIso φ ψ X).hom.app F) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The canonical degree-zero scalar comparison respects identity restriction. -/
theorem scalarRestrictionCohomologyZero_id (F : EtaleDerivedSections.ModuleSheaf X R) :
    (EtaleDerivedSections.cohomology X R 0).map
        ((sheafRestrictScalarsIdIso X).hom.app F) =
      (scalarRestrictionCohomologyZeroIso (RingHom.id R) X).hom.app F ≫
        (ModuleCat.restrictScalarsId R).hom.app
          ((EtaleDerivedSections.cohomology X R 0).obj F) := by
  apply (cancel_mono ((EtaleDerivedSections.cohomologyZeroIso X R).hom.app F)).1
  erw [(EtaleDerivedSections.cohomologyZeroIso X R).hom.naturality
    ((sheafRestrictScalarsIdIso X).hom.app F)]
  rw [Category.assoc]
  erw [← (ModuleCat.restrictScalarsId R).hom.naturality
    ((EtaleDerivedSections.cohomologyZeroIso X R).hom.app F)]
  rw [← Category.assoc, scalarRestrictionCohomologyZero_sections]
  rw [Category.assoc, ← scalarRestrictionSections_id]

/-- The canonical degree-zero comparison respects successive scalar restriction. -/
theorem scalarRestrictionCohomologyZero_comp (F : EtaleDerivedSections.ModuleSheaf X B) :
    (EtaleDerivedSections.cohomology X R 0).map
        ((sheafRestrictScalarsCompIso φ ψ X).hom.app F) ≫
        (scalarRestrictionCohomologyZeroIso φ X).hom.app
          ((sheafRestrictScalars ψ X).obj F) ≫
        (ModuleCat.restrictScalars φ).map
          ((scalarRestrictionCohomologyZeroIso ψ X).hom.app F) =
      (scalarRestrictionCohomologyZeroIso (ψ.comp φ) X).hom.app F ≫
        (ModuleCat.restrictScalarsComp φ ψ).hom.app
          ((EtaleDerivedSections.cohomology X B 0).obj F) := by
  apply (cancel_mono ((ModuleCat.restrictScalars φ).map
    ((ModuleCat.restrictScalars ψ).map
      ((EtaleDerivedSections.cohomologyZeroIso X B).hom.app F)))).1
  simp only [Category.assoc]
  rw [← Functor.map_comp, scalarRestrictionCohomologyZero_sections]
  rw [Functor.map_comp, ← Category.assoc
    ((scalarRestrictionCohomologyZeroIso φ X).hom.app _)]
  rw [scalarRestrictionCohomologyZero_sections]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((EtaleDerivedSections.cohomology X R 0).map _)]
  erw [(EtaleDerivedSections.cohomologyZeroIso X R).hom.naturality
    ((sheafRestrictScalarsCompIso φ ψ X).hom.app F)]
  simp only [Category.assoc]
  rw [scalarRestrictionSections_comp]
  erw [← (ModuleCat.restrictScalarsComp φ ψ).hom.naturality
    ((EtaleDerivedSections.cohomologyZeroIso X B).hom.app F)]
  simp only [← Category.assoc]
  rw [scalarRestrictionCohomologyZero_sections]

variable {X} {G : Type t} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- Apply cohomology over the fixed ring to the coefficient identity comparison. -/
def actionScalarCohomologyIdIso (q : ℕ) :
    scalarRestrictionFunctor (RingHom.id R) ρ ⋙ pullbackCohomologyFunctor R ρ q ≅
      pullbackCohomologyFunctor R ρ q :=
  Functor.isoWhiskerRight (scalarRestrictionIdIso ρ)
      (pullbackCohomologyFunctor R ρ q) ≪≫
    Functor.leftUnitor (pullbackCohomologyFunctor R ρ q)

/-- Split coefficient restriction before applying cohomology over the final ring. -/
def actionScalarCohomologyCompIso (q : ℕ) :
    scalarRestrictionFunctor (ψ.comp φ) ρ ⋙ pullbackCohomologyFunctor R ρ q ≅
      scalarRestrictionFunctor ψ ρ ⋙ scalarRestrictionFunctor φ ρ ⋙
        pullbackCohomologyFunctor R ρ q :=
  Functor.isoWhiskerRight (scalarRestrictionCompIso φ ψ ρ)
      (pullbackCohomologyFunctor R ρ q) ≪≫
    Functor.associator (scalarRestrictionFunctor ψ ρ) (scalarRestrictionFunctor φ ρ)
      (pullbackCohomologyFunctor R ρ q)

/-- The action identity comparison acts by equivariant cohomology. -/
@[simp] theorem actionScalarCohomologyIdIso_hom_app (q : ℕ) (F : EquivariantSheaf R ρ) :
    (actionScalarCohomologyIdIso ρ q).hom.app F =
      (pullbackCohomologyFunctor R ρ q).map ((scalarRestrictionIdIso ρ).hom.app F) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The action composition comparison acts by equivariant cohomology. -/
@[simp] theorem actionScalarCohomologyCompIso_hom_app (q : ℕ) (F : EquivariantSheaf B ρ) :
    (actionScalarCohomologyCompIso φ ψ ρ q).hom.app F =
      (pullbackCohomologyFunctor R ρ q).map
        ((scalarRestrictionCompIso φ ψ ρ).hom.app F) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

set_option maxHeartbeats 800000 in
/-- The canonical degree-zero scalar comparison respects identity restriction. -/
theorem scalarRestrictionCohomologyZeroFunctor_id (F : EquivariantSheaf R ρ) :
    (pullbackCohomologyFunctor R ρ 0).map
        ((scalarRestrictionIdIso ρ).hom.app F) =
      (scalarRestrictionCohomologyZeroFunctorIso (RingHom.id R) ρ).hom.app F ≫
        (actionRestrictScalarsIdIso G).hom.app
          ((pullbackCohomologyFunctor R ρ 0).obj F) := by
  apply (cancel_mono ((pullbackCohomologyZeroFunctorIso R ρ).hom.app F)).1
  erw [(pullbackCohomologyZeroFunctorIso R ρ).hom.naturality
    ((scalarRestrictionIdIso ρ).hom.app F)]
  rw [Category.assoc]
  erw [← (actionRestrictScalarsIdIso G).hom.naturality
    ((pullbackCohomologyZeroFunctorIso R ρ).hom.app F)]
  rw [← Category.assoc, scalarRestrictionCohomologyZeroFunctor_sections]
  rw [Category.assoc, ← scalarRestrictionSectionsFunctor_id]

set_option maxHeartbeats 800000 in
/-- The canonical degree-zero comparison respects successive scalar restriction. -/
theorem scalarRestrictionCohomologyZeroFunctor_comp (F : EquivariantSheaf B ρ) :
    (pullbackCohomologyFunctor R ρ 0).map
        ((scalarRestrictionCompIso φ ψ ρ).hom.app F) ≫
        (scalarRestrictionCohomologyZeroFunctorIso φ ρ).hom.app
          ((scalarRestrictionFunctor ψ ρ).obj F) ≫
        ((ModuleCat.restrictScalars φ).mapAction G).map
          ((scalarRestrictionCohomologyZeroFunctorIso ψ ρ).hom.app F) =
      (scalarRestrictionCohomologyZeroFunctorIso (ψ.comp φ) ρ).hom.app F ≫
        (actionRestrictScalarsCompIso φ ψ G).hom.app
          ((pullbackCohomologyFunctor B ρ 0).obj F) := by
  apply (cancel_mono (((ModuleCat.restrictScalars φ).mapAction G).map
    (((ModuleCat.restrictScalars ψ).mapAction G).map
      ((pullbackCohomologyZeroFunctorIso B ρ).hom.app F)))).1
  simp only [Category.assoc]
  rw [← Functor.map_comp, scalarRestrictionCohomologyZeroFunctor_sections]
  rw [Functor.map_comp, ← Category.assoc
    ((scalarRestrictionCohomologyZeroFunctorIso φ ρ).hom.app _)]
  rw [scalarRestrictionCohomologyZeroFunctor_sections]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((pullbackCohomologyFunctor R ρ 0).map _)]
  erw [(pullbackCohomologyZeroFunctorIso R ρ).hom.naturality
    ((scalarRestrictionCompIso φ ψ ρ).hom.app F)]
  simp only [Category.assoc]
  rw [scalarRestrictionSectionsFunctor_comp]
  erw [← (actionRestrictScalarsCompIso φ ψ G).hom.naturality
    ((pullbackCohomologyZeroFunctorIso B ρ).hom.app F)]
  simp only [← Category.assoc]
  rw [scalarRestrictionCohomologyZeroFunctor_sections]

variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

namespace EquivariantCoefficientDiagram

/-- Apply diagram cohomology to the coefficient identity comparison. -/
def scalarCohomologyIdIso (q : ℕ) :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) (RingHom.id R) ⋙
        cohomologyFunctor q ≅ cohomologyFunctor q :=
  Functor.isoWhiskerRight restrictScalarsIdIso (cohomologyFunctor q) ≪≫
    Functor.leftUnitor (cohomologyFunctor q)

/-- Split coefficient restriction before taking cohomology over the final ring. -/
def scalarCohomologyCompIso (q : ℕ) :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) (ψ.comp φ) ⋙
        cohomologyFunctor q ≅
      restrictScalarsFunctor ψ ⋙ restrictScalarsFunctor φ ⋙ cohomologyFunctor q :=
  Functor.isoWhiskerRight (restrictScalarsCompIso φ ψ) (cohomologyFunctor q) ≪≫
    Functor.associator (restrictScalarsFunctor ψ) (restrictScalarsFunctor φ)
      (cohomologyFunctor q)

/-- The diagram identity comparison is the image of the coefficient comparison. -/
@[simp] theorem scalarCohomologyIdIso_hom_app
    (q : ℕ) (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (scalarCohomologyIdIso q).hom.app D =
      (cohomologyFunctor q).map (restrictScalarsIdIso.hom.app D) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The diagram composition comparison is the image of the coefficient comparison. -/
@[simp] theorem scalarCohomologyCompIso_hom_app
    (q : ℕ) (D : EquivariantCoefficientDiagram B S ρ hρ) :
    (scalarCohomologyCompIso φ ψ q).hom.app D =
      (cohomologyFunctor q).map ((restrictScalarsCompIso φ ψ).hom.app D) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Canonical degree-zero scalar restriction on diagrams respects the identity ring map. -/
theorem restrictScalarsCohomologyZero_id (D : EquivariantCoefficientDiagram R S ρ hρ) :
    (cohomologyFunctor 0).map (restrictScalarsIdIso.hom.app D) =
      (restrictScalarsCohomologyZeroFunctorIso (RingHom.id R)).hom.app D ≫
        (actionDiagramRestrictScalarsIdIso G).hom.app (D.cohomology 0) := by
  apply NatTrans.ext
  funext i
  exact scalarRestrictionCohomologyZeroFunctor_id (ρ i) (D.obj i)

/-- Canonical degree-zero scalar restriction on diagrams respects ring-map composition. -/
theorem restrictScalarsCohomologyZero_comp (D : EquivariantCoefficientDiagram B S ρ hρ) :
    (cohomologyFunctor 0).map ((restrictScalarsCompIso φ ψ).hom.app D) ≫
        (restrictScalarsCohomologyZeroFunctorIso φ).hom.app (restrictScalars ψ D) ≫
        (actionDiagramRestrictScalarsFunctor φ G).map
          ((restrictScalarsCohomologyZeroFunctorIso ψ).hom.app D) =
      (restrictScalarsCohomologyZeroFunctorIso (ψ.comp φ)).hom.app D ≫
        (actionDiagramRestrictScalarsCompIso φ ψ G).hom.app (D.cohomology 0) := by
  apply NatTrans.ext
  funext i
  exact scalarRestrictionCohomologyZeroFunctor_comp φ ψ (ρ i) (D.obj i)

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction

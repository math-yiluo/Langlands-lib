import Langlands.Geometry.EtaleGeometricCoefficientPullback
import Langlands.Geometry.EtaleInverseImageCoherence

/-! # Compatible coefficients over arbitrary scheme diagrams -/

noncomputable section

universe u v w wS wR

namespace Langlands.Geometry.EtaleInverseImage

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (R : Type u) [CommRing R]

/-- The actual geometric equality comparison is the identity for reflexivity. -/
@[simp] theorem inverseImageCongr_refl (f : Z ⟶ X) :
    inverseImageCongr R (rfl : f = f) = Iso.refl _ := by
  apply Iso.ext
  apply (conjugateEquiv (inverseImageAdjunction f R)
    (inverseImageAdjunction f R)).injective
  rw [conjugate_inverseImageCongr]
  simp only [Iso.refl_hom, conjugateEquiv_id]
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have he :
      (Langlands.Shimura.Coefficients.etaleObjectPullbackCongr
        (rfl : f = f)).hom.app U.unop = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change _ = 𝟙 (Limits.pullback U.unop.hom f)
    apply Limits.pullback.hom_ext <;> simp
  change F.obj.map
    ((Langlands.Shimura.Coefficients.etaleObjectPullbackCongr
      (rfl : f = f)).hom.app U.unop).op = 𝟙 _
  rw [he]
  exact F.obj.map_id _

end Langlands.Geometry.EtaleInverseImage

namespace Langlands.Geometry.EtaleGeometricDiagram

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections EtaleDerivedGlobalPullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (R : Type u) [CommRing R]

section
variable [HasDerivedCategory.{wS} (ModuleSheaf X R)]
  [HasDerivedCategory.{wS} (ModuleSheaf Z R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
/-- Derived geometric pullback respects equality of the base morphism through
the actual inverse-image equality comparison. -/
theorem sheafDerivedPullback_congr {f g : Z ⟶ X} (h : f = g)
    (F : ModuleSheaf X R) :
    (sheafDerivedPullback f R).app F ≫
        (EtaleDerivedSectionsPlus.derivedSections Z R).map
          ((inverseImageCongr R h).hom.app F) =
      (sheafDerivedPullback g R).app F := by
  subst g
  simp

end

variable {J : Type v} [Category.{w} J] (S : J ⥤ Scheme.{u}ᵒᵖ)

/-- Actual geometric inverse image along an arrow of an arbitrary
contravariant scheme diagram. -/
abbrev diagramInverseImage {i j : J} (a : i ⟶ j) :=
  inverseImage (S.map a).unop R

/-- The identity comparison retains transport of the diagram's identity law. -/
def diagramInverseImageId (i : J) :
    diagramInverseImage R S (𝟙 i) ≅ 𝟭 (ModuleSheaf (S.obj i).unop R) :=
  inverseImageCongr R (congrArg Quiver.Hom.unop (S.map_id i)) ≪≫
    inverseImageId R (S.obj i).unop

/-- The composition comparison retains transport of the diagram's
composition law. -/
def diagramInverseImageComp {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    diagramInverseImage R S a ⋙ diagramInverseImage R S b ≅
      diagramInverseImage R S (a ≫ b) :=
  inverseImageComp R (S.map a).unop (S.map b).unop ≪≫
    inverseImageCongr R (congrArg Quiver.Hom.unop (S.map_comp a b)).symm

/-- Actual module sheaves and compatible inverse-image coefficient maps.
The fields contain no cohomology objects, maps or assumed comparison laws. -/
structure CoefficientDiagram where
  obj (i : J) : ModuleSheaf (S.obj i).unop R
  map {i j : J} (a : i ⟶ j) : (diagramInverseImage R S a).obj (obj i) ⟶ obj j
  map_id (i : J) : map (𝟙 i) = (diagramInverseImageId R S i).hom.app (obj i)
  map_comp {i j k : J} (a : i ⟶ j) (b : j ⟶ k) :
    (diagramInverseImageComp R S a b).hom.app (obj i) ≫ map (a ≫ b) =
      (diagramInverseImage R S b).map (map a) ≫ map b

namespace CoefficientDiagram

variable {R S}

/-- Pointwise sheaf morphisms commuting with every geometric transition. -/
@[ext] structure Hom (D E : CoefficientDiagram R S) where
  app (i : J) : D.obj i ⟶ E.obj i
  comm {i j : J} (a : i ⟶ j) :
    D.map a ≫ app j = (diagramInverseImage R S a).map (app i) ≫ E.map a

/-- The pointwise identity respects every coefficient transition. -/
def Hom.id (D : CoefficientDiagram R S) : Hom D D where
  app i := 𝟙 (D.obj i)
  comm a := by simp

/-- The pointwise composite respects every coefficient transition. -/
def Hom.comp {D E F : CoefficientDiagram R S} (α : Hom D E) (β : Hom E F) :
    Hom D F where
  app i := α.app i ≫ β.app i
  comm a := by
    rw [← Category.assoc, α.comm, Category.assoc, β.comm]
    simp only [Functor.map_comp, Category.assoc]

instance : Category (CoefficientDiagram R S) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp α := by ext i; simp [Hom.id, Hom.comp]
  comp_id α := by ext i; simp [Hom.id, Hom.comp]
  assoc α β γ := by ext i; simp [Hom.comp, Category.assoc]

@[simp] theorem id_app (D : CoefficientDiagram R S) (i : J) :
    (𝟙 D : D ⟶ D).app i = 𝟙 (D.obj i) := rfl

@[simp] theorem comp_app {D E F : CoefficientDiagram R S}
    (α : D ⟶ E) (β : E ⟶ F) (i : J) :
    (α ≫ β).app i = α.app i ≫ β.app i := rfl

/-- Evaluation returns the actual sheaf and sheaf morphism at a vertex. -/
def evaluation (i : J) :
    CoefficientDiagram R S ⥤ ModuleSheaf (S.obj i).unop R where
  obj D := D.obj i
  map α := α.app i

end CoefficientDiagram

variable [∀ i : J, HasDerivedCategory.{wS} (ModuleSheaf (S.obj i).unop R)]
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Derived pullback along a diagram identity, including its actual
geometric coefficient identification. -/
theorem diagramDerivedPullback_id (i : J) (F : ModuleSheaf (S.obj i).unop R) :
    (sheafDerivedPullback (S.map (𝟙 i)).unop R).app F ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map
          ((diagramInverseImageId R S i).hom.app F) = 𝟙 _ := by
  dsimp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.map_comp, ← Category.assoc, sheafDerivedPullback_congr]
  exact sheafDerivedPullback_id R F

/-- Successive derived pullbacks agree with the diagram composite through
the constructed inverse-image comparison. -/
theorem diagramDerivedPullback_comp {i j k : J} (a : i ⟶ j) (b : j ⟶ k)
    (F : ModuleSheaf (S.obj i).unop R) :
    (sheafDerivedPullback (S.map a).unop R).app F ≫
        (sheafDerivedPullback (S.map b).unop R).app
          ((diagramInverseImage R S a).obj F) ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj k).unop R).map
          ((diagramInverseImageComp R S a b).hom.app F) =
      (sheafDerivedPullback (S.map (a ≫ b)).unop R).app F := by
  dsimp only [diagramInverseImageComp, Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.map_comp]
  have e : (S.map b).unop ≫ (S.map a).unop = (S.map (a ≫ b)).unop :=
    (congrArg Quiver.Hom.unop (S.map_comp a b)).symm
  calc
    _ = (sheafDerivedPullback ((S.map b).unop ≫ (S.map a).unop) R).app F ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj k).unop R).map
          ((inverseImageCongr R e).hom.app F) := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫
          (EtaleDerivedSectionsPlus.derivedSections (S.obj k).unop R).map
            ((inverseImageCongr R e).hom.app F))
        (sheafDerivedPullback_comp R (S.map a).unop (S.map b).unop F)
    _ = _ := sheafDerivedPullback_congr R e F

namespace CoefficientDiagram

variable {R S}

/-- Bounded-below derived sections with actual geometric coefficient maps,
over every arrow of an arbitrary scheme diagram. -/
def derivedSections (D : CoefficientDiagram R S) :
    J ⥤ DerivedCategory.Plus (ModuleCat.{u} R) where
  obj i := (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).obj (D.obj i)
  map a := sheafDerivedPullbackWithCoefficients (S.map a).unop R (D.map a)
  map_id i := by
    dsimp only [sheafDerivedPullbackWithCoefficients]
    rw [D.map_id]
    exact diagramDerivedPullback_id R S i (D.obj i)
  map_comp {i j k} a b := by
    dsimp only [sheafDerivedPullbackWithCoefficients]
    rw [← diagramDerivedPullback_comp R S a b (D.obj i)]
    simp only [Category.assoc]
    rw [← Functor.map_comp, D.map_comp]
    simp only [Functor.map_comp]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun t => (sheafDerivedPullback (S.map a).unop R).app (D.obj i) ≫ t ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj k).unop R).map (D.map b))
      ((sheafDerivedPullback (S.map b).unop R).naturality (D.map a)).symm

/-- Compatible sheaf morphisms induce natural maps of derived-section
diagrams. -/
def derivedSectionsMap {D E : CoefficientDiagram R S} (α : D ⟶ E) :
    D.derivedSections ⟶ E.derivedSections where
  app i := (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map (α.app i)
  naturality {i j} a := by
    dsimp only [derivedSections, sheafDerivedPullbackWithCoefficients]
    simp only [Category.assoc]
    rw [← Functor.map_comp, α.comm, Functor.map_comp]
    simpa only [Category.assoc, Functor.comp_map] using congrArg
      (fun t => t ≫
        (EtaleDerivedSectionsPlus.derivedSections (S.obj j).unop R).map (E.map a))
      ((sheafDerivedPullback (S.map a).unop R).naturality (α.app i)).symm

/-- Derived sections are functorial in actual compatible coefficients. -/
def derivedSectionsFunctor :
    CoefficientDiagram R S ⥤ (J ⥤ DerivedCategory.Plus (ModuleCat.{u} R)) where
  obj D := D.derivedSections
  map α := derivedSectionsMap α
  map_id D := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map_id (D.obj i)
  map_comp α β := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSectionsPlus.derivedSections (S.obj i).unop R).map_comp
      (α.app i) (β.app i)

/-- Ordinary cohomology with transition maps transported from actual
derived sections along the canonical homology isomorphisms. -/
def cohomology (D : CoefficientDiagram R S) (q : ℕ) : J ⥤ ModuleCat.{u} R where
  obj i := (EtaleDerivedSections.cohomology (S.obj i).unop R q).obj (D.obj i)
  map {i j} a :=
    (EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R q).inv.app (D.obj i) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
        (D.derivedSections.map a) ≫
      (EtaleDerivedSectionsPlus.homologyNatIso (S.obj j).unop R q).hom.app (D.obj j)
  map_id i := by
    rw [CategoryTheory.Functor.map_id]
    erw [CategoryTheory.Functor.map_id]
    simp
  map_comp a b := by
    rw [Functor.map_comp, Functor.map_comp]
    simp [Category.assoc]

/-- The transported transition is exactly the constructed geometric
ordinary-cohomology pullback with the given target coefficient map. -/
theorem cohomology_map (D : CoefficientDiagram R S) (q : ℕ)
    {i j : J} (a : i ⟶ j) :
    (D.cohomology q).map a =
      cohomologyPullbackWithCoefficients (S.map a).unop R q (D.map a) := by
  dsimp only [cohomology, derivedSections]
  rw [sheafDerivedPullbackWithCoefficients_homology]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- Ordinary cohomology is recovered naturally along every diagram arrow. -/
def derivedSectionsHomologyIso (D : CoefficientDiagram R S) (q : ℕ) :
    D.derivedSections ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q ≅
      D.cohomology q :=
  NatIso.ofComponents
    (fun i => (EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R q).app (D.obj i))
    (fun {i j} a => by
      dsimp only [cohomology, Iso.app_hom]
      simp only [← Category.assoc, Iso.hom_inv_id_app]
      erw [Category.id_comp]
      rfl)

/-- Cohomology of compatible coefficient morphisms, transported from
derived sections through the canonical homology identification. -/
def cohomologyFunctor (q : ℕ) :
    CoefficientDiagram R S ⥤ (J ⥤ ModuleCat.{u} R) where
  obj D := D.cohomology q
  map {D E} α :=
    { app i := (EtaleDerivedSections.cohomology (S.obj i).unop R q).map (α.app i)
      naturality {i j} a := by
        rw [cohomology_map, cohomology_map]
        dsimp only [cohomologyPullbackWithCoefficients]
        simp only [Category.assoc]
        rw [← Functor.map_comp, α.comm, Functor.map_comp]
        simpa only [Category.assoc, Functor.comp_map] using congrArg
          (fun t => t ≫ (EtaleDerivedSections.cohomology (S.obj j).unop R q).map
            (E.map a))
          ((cohomologyPullback (S.map a).unop R q).naturality (α.app i)).symm }
  map_id D := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSections.cohomology (S.obj i).unop R q).map_id (D.obj i)
  map_comp α β := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSections.cohomology (S.obj i).unop R q).map_comp
      (α.app i) (β.app i)

/-- The cohomology functor acts on coefficient morphisms by the actual
ordinary-cohomology functor at each vertex. -/
theorem cohomologyFunctor_map_app (q : ℕ) {D E : CoefficientDiagram R S}
    (α : D ⟶ E) (i : J) :
    ((cohomologyFunctor q).map α).app i =
      (EtaleDerivedSections.cohomology (S.obj i).unop R q).map (α.app i) := rfl

/-- Homology recovery is natural also in the compatible coefficients. -/
def derivedSectionsHomologyFunctorIso (q : ℕ) :
    derivedSectionsFunctor (R := R) (S := S) ⋙
        (Functor.whiskeringRight J (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q) ≅
      cohomologyFunctor q :=
  NatIso.ofComponents (fun D => derivedSectionsHomologyIso D q)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (EtaleDerivedSectionsPlus.homologyNatIso (S.obj i).unop R q).hom.naturality
        (α.app i))

/-- Actual sections with transition maps transported from degree-zero
homology of the actual derived-section diagram. -/
def sections (D : CoefficientDiagram R S) : J ⥤ ModuleCat.{u} R where
  obj i := (EtaleDerivedSections.sections (S.obj i).unop R).obj (D.obj i)
  map {i j} a :=
    (EtaleDerivedSectionsPlus.homologyZeroIso (S.obj i).unop R).inv.app (D.obj i) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (D.derivedSections.map a) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso (S.obj j).unop R).hom.app (D.obj j)
  map_id i := by
    rw [CategoryTheory.Functor.map_id]
    erw [CategoryTheory.Functor.map_id]
    simp
  map_comp a b := by
    rw [Functor.map_comp, Functor.map_comp]
    simp [Category.assoc]

/-- Every section transition is actual geometric section pullback followed
by the given target coefficient map. -/
theorem sections_map (D : CoefficientDiagram R S) {i j : J} (a : i ⟶ j) :
    D.sections.map a =
      sectionsPullbackWithCoefficients (S.map a).unop R (D.map a) := by
  dsimp only [sections, derivedSections]
  rw [sheafDerivedPullbackWithCoefficients_zero]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- Degree-zero homology recovers sections naturally along the geometric
arrows. -/
def derivedSectionsZeroIso (D : CoefficientDiagram R S) :
    D.derivedSections ⋙ DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0 ≅
      D.sections :=
  NatIso.ofComponents
    (fun i => (EtaleDerivedSectionsPlus.homologyZeroIso (S.obj i).unop R).app (D.obj i))
    (fun {i j} a => by
      dsimp only [sections, Iso.app_hom]
      simp only [← Category.assoc, Iso.hom_inv_id_app]
      erw [Category.id_comp]
      rfl)

/-- Sections of compatible coefficient morphisms, through the canonical
degree-zero comparison. -/
def sectionsFunctor : CoefficientDiagram R S ⥤ (J ⥤ ModuleCat.{u} R) where
  obj D := D.sections
  map {D E} α :=
    { app i := (EtaleDerivedSections.sections (S.obj i).unop R).map (α.app i)
      naturality {i j} a := by
        rw [sections_map, sections_map]
        dsimp only [sectionsPullbackWithCoefficients]
        simp only [Category.assoc]
        rw [← Functor.map_comp, α.comm, Functor.map_comp]
        simpa only [Category.assoc, Functor.comp_map] using congrArg
          (fun t => t ≫ (EtaleDerivedSections.sections (S.obj j).unop R).map (E.map a))
          ((sectionsPullback (S.map a).unop R).naturality (α.app i)).symm }
  map_id D := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSections.sections (S.obj i).unop R).map_id (D.obj i)
  map_comp α β := by
    apply NatTrans.ext
    funext i
    exact (EtaleDerivedSections.sections (S.obj i).unop R).map_comp
      (α.app i) (β.app i)

/-- The section functor acts by actual sections on each coefficient
morphism. -/
theorem sectionsFunctor_map_app {D E : CoefficientDiagram R S}
    (α : D ⟶ E) (i : J) :
    (sectionsFunctor.map α).app i =
      (EtaleDerivedSections.sections (S.obj i).unop R).map (α.app i) := rfl

/-- The zero-degree comparison is natural in compatible coefficients. -/
def derivedSectionsZeroFunctorIso :
    derivedSectionsFunctor (R := R) (S := S) ⋙
        (Functor.whiskeringRight J (DerivedCategory.Plus (ModuleCat.{u} R))
          (ModuleCat.{u} R)).obj
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0) ≅
      sectionsFunctor :=
  NatIso.ofComponents (fun D => derivedSectionsZeroIso D)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (EtaleDerivedSectionsPlus.homologyZeroIso (S.obj i).unop R).hom.naturality
        (α.app i))

/-- Ordinary degree-zero cohomology is identified with actual sections
naturally in both the scheme arrows and the coefficients. -/
def cohomologyZeroFunctorIso : cohomologyFunctor (R := R) (S := S) 0 ≅ sectionsFunctor :=
  (derivedSectionsHomologyFunctorIso 0).symm ≪≫ derivedSectionsZeroFunctorIso

end CoefficientDiagram

end Langlands.Geometry.EtaleGeometricDiagram

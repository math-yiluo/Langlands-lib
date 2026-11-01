import Langlands.Geometry.EtaleGeometricCoefficientDiagram
import Langlands.Geometry.EtaleInverseImageRestrictionCoherence
import Langlands.Geometry.EtaleCohomologyDiagramFunctor

/-! # Geometric and restriction coefficient diagrams along etale maps -/

noncomputable section

universe u v w

namespace Langlands.Geometry.EtaleGeometricDiagram

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R]
variable {J : Type v} [Category.{w} J] (S : J ⥤ Scheme.{u}ᵒᵖ)
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]

/-- The constructed inverse-image comparison along a diagram arrow. -/
abbrev diagramInverseImageIsoRestriction {i j : J} (a : i ⟶ j) :
    diagramInverseImage R S a ≅ EtalePullback.diagramRestriction R S a :=
  inverseImageIsoRestriction (S.map a).unop R

/-- The arrow comparisons intertwine the actual diagram identity constraints. -/
theorem diagramInverseImageIsoRestriction_id (i : J)
    (F : ModuleSheaf (S.obj i).unop R) :
    (diagramInverseImageIsoRestriction R S (𝟙 i)).hom.app F ≫
        (EtalePullback.diagramRestrictionId R S i).hom.app F =
      (diagramInverseImageId R S i).hom.app F := by
  have h := congrArg (fun t => t.app F)
    (inverseImageIsoRestriction_congr R
      (congrArg Quiver.Hom.unop (S.map_id i)))
  simp only [NatTrans.comp_app] at h
  dsimp only [diagramInverseImageId, EtalePullback.diagramRestrictionId,
    Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc, ← h, Category.assoc]
  simpa only [NatTrans.comp_app, CategoryTheory.unop_id] using
    congrArg (fun t => (inverseImageCongr R
      (congrArg Quiver.Hom.unop (S.map_id i))).hom.app F ≫ t)
      (congrArg (fun t => t.app F) (inverseImageIsoRestriction_id R (S.obj i).unop))

/-- The arrow comparisons intertwine the actual diagram composition constraints. -/
theorem diagramInverseImageIsoRestriction_comp {i j k : J}
    (a : i ⟶ j) (b : j ⟶ k) (F : ModuleSheaf (S.obj i).unop R) :
    (diagramInverseImageComp R S a b).hom.app F ≫
        (diagramInverseImageIsoRestriction R S (a ≫ b)).hom.app F =
      (diagramInverseImage R S b).map
          ((diagramInverseImageIsoRestriction R S a).hom.app F) ≫
        (diagramInverseImageIsoRestriction R S b).hom.app
          ((EtalePullback.diagramRestriction R S a).obj F) ≫
        (EtalePullback.diagramRestrictionComp R S a b).hom.app F := by
  dsimp only [diagramInverseImageComp, EtalePullback.diagramRestrictionComp,
    Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc]
  rw [← NatTrans.comp_app, inverseImageIsoRestriction_congr, NatTrans.comp_app]
  rw [← Category.assoc, ← NatTrans.comp_app, inverseImageIsoRestriction_comp]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]

/-- The inverse comparisons intertwine the diagram composition constraints. -/
theorem diagramInverseImageIsoRestriction_comp_inv {i j k : J}
    (a : i ⟶ j) (b : j ⟶ k) (F : ModuleSheaf (S.obj i).unop R) :
    (EtalePullback.diagramRestrictionComp R S a b).hom.app F ≫
        (diagramInverseImageIsoRestriction R S (a ≫ b)).inv.app F =
      (diagramInverseImageIsoRestriction R S b).inv.app
          ((EtalePullback.diagramRestriction R S a).obj F) ≫
        (diagramInverseImage R S b).map
          ((diagramInverseImageIsoRestriction R S a).inv.app F) ≫
        (diagramInverseImageComp R S a b).hom.app F := by
  apply (cancel_mono
    ((diagramInverseImageIsoRestriction R S (a ≫ b)).hom.app F)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [diagramInverseImageIsoRestriction_comp]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp

namespace CoefficientDiagram

variable {R S}

/-- Convert genuine restriction coefficients to genuine geometric coefficients. -/
def ofRestriction (D : EtalePullback.CoefficientDiagram R S) :
    CoefficientDiagram R S where
  obj i := D.obj i
  map a := (diagramInverseImageIsoRestriction R S a).hom.app (D.obj _) ≫ D.map a
  map_id i := by
    rw [D.map_id]
    exact diagramInverseImageIsoRestriction_id R S i (D.obj i)
  map_comp {i j k} a b := by
    rw [← Category.assoc, diagramInverseImageIsoRestriction_comp]
    simp only [Category.assoc]
    rw [D.map_comp]
    rw [← Category.assoc ((diagramInverseImageIsoRestriction R S b).hom.app _),
      ← (diagramInverseImageIsoRestriction R S b).hom.naturality (D.map a)]
    simp only [Functor.map_comp, Category.assoc]

/-- Convert genuine geometric coefficients to genuine restriction coefficients. -/
def toRestriction (D : CoefficientDiagram R S) :
    EtalePullback.CoefficientDiagram R S where
  obj i := D.obj i
  map a := (diagramInverseImageIsoRestriction R S a).inv.app (D.obj _) ≫ D.map a
  map_id i := by
    rw [D.map_id, ← diagramInverseImageIsoRestriction_id R S i (D.obj i)]
    simp
  map_comp {i j k} a b := by
    rw [← Category.assoc, diagramInverseImageIsoRestriction_comp_inv]
    simp only [Category.assoc]
    rw [D.map_comp]
    rw [← Functor.map_comp_assoc]
    rw [← Category.assoc, ← (diagramInverseImageIsoRestriction R S b).inv.naturality]
    simp only [Category.assoc]

/-- Restriction-to-geometric transport preserves the component sheaf morphisms. -/
def ofRestrictionFunctor :
    EtalePullback.CoefficientDiagram R S ⥤ CoefficientDiagram R S where
  obj := ofRestriction
  map {D E} α :=
    { app i := α.app i
      comm a := by
        dsimp only [ofRestriction]
        rw [Category.assoc, α.comm, ← Category.assoc,
          ← (diagramInverseImageIsoRestriction R S a).hom.naturality]
        simp only [Category.assoc] }
  map_id D := by apply Hom.ext; rfl
  map_comp α β := by apply Hom.ext; rfl

/-- Geometric-to-restriction transport preserves the component sheaf morphisms. -/
def toRestrictionFunctor :
    CoefficientDiagram R S ⥤ EtalePullback.CoefficientDiagram R S where
  obj := toRestriction
  map {D E} α :=
    { app i := α.app i
      comm a := by
        dsimp only [toRestriction]
        rw [Category.assoc, α.comm, ← Category.assoc,
          ← (diagramInverseImageIsoRestriction R S a).inv.naturality]
        simp only [Category.assoc] }
  map_id D := by apply EtalePullback.CoefficientDiagram.Hom.ext; rfl
  map_comp α β := by apply EtalePullback.CoefficientDiagram.Hom.ext; rfl

/-- Transport to restriction and back has identity component sheaf maps. -/
def geometricRoundTripIso (D : CoefficientDiagram R S) :
    ofRestriction (toRestriction D) ≅ D where
  hom :=
    { app i := 𝟙 (D.obj i)
      comm a := by simp [ofRestriction, toRestriction] }
  inv :=
    { app i := 𝟙 (D.obj i)
      comm a := by simp [ofRestriction, toRestriction] }
  hom_inv_id := by
    apply Hom.ext
    funext i
    change 𝟙 (D.obj i) ≫ 𝟙 (D.obj i) = 𝟙 (D.obj i)
    simp
  inv_hom_id := by
    apply Hom.ext
    funext i
    change 𝟙 (D.obj i) ≫ 𝟙 (D.obj i) = 𝟙 (D.obj i)
    simp

/-- Transport to geometric inverse image and back has identity sheaf maps. -/
def restrictionRoundTripIso (D : EtalePullback.CoefficientDiagram R S) :
    toRestriction (ofRestriction D) ≅ D where
  hom :=
    { app i := 𝟙 (D.obj i)
      comm a := by simp [ofRestriction, toRestriction] }
  inv :=
    { app i := 𝟙 (D.obj i)
      comm a := by simp [ofRestriction, toRestriction] }
  hom_inv_id := by
    apply EtalePullback.CoefficientDiagram.Hom.ext
    funext i
    change 𝟙 (D.obj i) ≫ 𝟙 (D.obj i) = 𝟙 (D.obj i)
    simp
  inv_hom_id := by
    apply EtalePullback.CoefficientDiagram.Hom.ext
    funext i
    change 𝟙 (D.obj i) ≫ 𝟙 (D.obj i) = 𝟙 (D.obj i)
    simp

/-- Actual geometric and restriction coefficient categories are equivalent. -/
def restrictionEquivalence :
    CoefficientDiagram R S ≌ EtalePullback.CoefficientDiagram R S where
  functor := toRestrictionFunctor
  inverse := ofRestrictionFunctor
  unitIso := NatIso.ofComponents (fun D => (geometricRoundTripIso D).symm)
    (fun α => by apply Hom.ext; funext i; simp [geometricRoundTripIso, toRestrictionFunctor,
      ofRestrictionFunctor])
  counitIso := NatIso.ofComponents restrictionRoundTripIso
    (fun α => by
      apply EtalePullback.CoefficientDiagram.Hom.ext
      funext i
      change α.app i ≫ 𝟙 _ = 𝟙 _ ≫ α.app i
      simp)
  functor_unitIso_comp D := by
    apply EtalePullback.CoefficientDiagram.Hom.ext
    funext i
    change 𝟙 (D.obj i) ≫ 𝟙 (D.obj i) = 𝟙 (D.obj i)
    simp

/-- Transport commutes with evaluation at each actual coefficient sheaf. -/
def toRestrictionEvaluationIso (i : J) :
    toRestrictionFunctor (R := R) (S := S) ⋙
        EtalePullback.CoefficientDiagram.evaluation i ≅ evaluation i :=
  Iso.refl _

/-- Reverse transport also commutes with evaluation at each coefficient sheaf. -/
def ofRestrictionEvaluationIso (i : J) :
    ofRestrictionFunctor (R := R) (S := S) ⋙ evaluation i ≅
      EtalePullback.CoefficientDiagram.evaluation i :=
  Iso.refl _

end CoefficientDiagram

end Langlands.Geometry.EtaleGeometricDiagram

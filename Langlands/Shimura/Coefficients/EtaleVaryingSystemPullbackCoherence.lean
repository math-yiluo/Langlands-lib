import Langlands.Shimura.Coefficients.EtaleVaryingSystemPullback
import Langlands.Shimura.Coefficients.EtaleConstantAssociatedPullbackCoherence
import Langlands.Shimura.Coefficients.EtaleTorsorPullbackFunctoriality
import Langlands.Shimura.Coefficients.VaryingSystemCoverChange

/-! # Identity and composition of whole varying-torsor system base change -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z W : Scheme.{u}}
variable (f : Z ⟶ X) [Etale f] (g : W ⟶ Z) [Etale g]
variable (R : Type u) [CommRing R]
variable {I : Type uI} [Category.{vI} I]

/-- Restriction identity applied to entire sheaf diagrams. -/
def etaleSheafDiagramRestrictionId (X : Scheme.{u}) :
    (Functor.whiskeringRight I _ _).obj
        (EtalePullback.restriction (𝟙 X) (ModuleCat.{u} R)) ≅
      𝟭 (I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  (Functor.whiskeringRight I _ _).mapIso
      (EtalePullback.restrictionId (ModuleCat.{u} R)) ≪≫
    Functor.whiskeringRightObjIdIso

/-- Restriction composition applied to entire sheaf diagrams. -/
def etaleSheafDiagramRestrictionComp :
    (Functor.whiskeringRight I _ _).obj
        (EtalePullback.restriction f (ModuleCat.{u} R)) ⋙
      (Functor.whiskeringRight I _ _).obj
        (EtalePullback.restriction g (ModuleCat.{u} R)) ≅
    (Functor.whiskeringRight I _ _).obj
      (EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)) :=
  Functor.whiskeringRightObjCompIso _ _ ≪≫
    (Functor.whiskeringRight I _ _).mapIso
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g)

@[simp] theorem etaleSheafDiagramRestrictionId_hom_app_app (X : Scheme.{u})
    (F : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (i : I) :
    ((etaleSheafDiagramRestrictionId (I := I) R X).hom.app F).app i =
      (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app (F.obj i) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

@[simp] theorem etaleSheafDiagramRestrictionComp_hom_app_app
    (F : I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (i : I) :
    ((etaleSheafDiagramRestrictionComp (I := I) f g R).hom.app F).app i =
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app (F.obj i) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

variable {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))

/-- Evaluating geometric diagram identity gives the actual identity-cover map. -/
@[simp] theorem etaleTorsorDiagramPullbackId_evaluation (i : I) :
    (EquivariantDiagram.evaluation i).map
        ((etaleTorsorDiagramPullbackId D).hom.app Y) =
      (etaleTorsorPullbackId X (D.obj i)).hom.app (Y.action i) := by
  apply Action.Hom.ext
  apply MorphismProperty.Over.Hom.ext
  change pullback.fst (Y.action i).V.hom (𝟙 X) ≫ 𝟙 _ = _
  exact Category.comp_id _

omit [Etale f] [Etale g] in
/-- Evaluating geometric diagram composition gives its actual cover comparison. -/
@[simp] theorem etaleTorsorDiagramPullbackComp_evaluation (i : I) :
    (EquivariantDiagram.evaluation i).map
        ((etaleTorsorDiagramPullbackComp f D g).hom.app Y) =
      (etaleTorsorPullbackComp f (D.obj i) g).hom.app (Y.action i) := rfl

/-- Two restrictions compare naturally with the system on the single-pullback
cover diagram, using the structural restriction-composition isomorphism. -/
def etaleAssociatedVaryingSystemPullbackComp :
    (etaleAssociatedVaryingSystemFunctor (R := R) X Y hY ⋙
        (Functor.whiskeringRight I _ _).obj
          (EtalePullback.restriction f (ModuleCat.{u} R))) ⋙
      (Functor.whiskeringRight I _ _).obj
        (EtalePullback.restriction g (ModuleCat.{u} R)) ≅
    etaleAssociatedVaryingSystemFunctor W
      ((etaleTorsorDiagramPullback (g ≫ f) D).obj Y)
      (etaleTorsorDiagramPullback_isFiniteGeometricTorsor (g ≫ f) D Y hY) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleAssociatedVaryingSystemFunctor (R := R) X Y hY)
      (etaleSheafDiagramRestrictionComp (I := I) f g R) ≪≫
    etaleAssociatedVaryingSystemPullback (g ≫ f) R Y hY

@[simp] theorem etaleAssociatedVaryingSystemPullbackComp_hom_app_app
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    ((etaleAssociatedVaryingSystemPullbackComp f g R Y hY).hom.app M).app i =
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app
          ((etaleAssociatedFunctor X (Y.action i)).obj (M.action i)) ≫
        (etaleConstantAssociatedPullback (g ≫ f) R (Y.action i)).hom.app (M.action i) := by
  change 𝟙 _ ≫ _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- Identity system base change is restriction identity followed by
contravariant change along the genuine identity-pullback projection. -/
@[reassoc] theorem etaleAssociatedVaryingSystemPullback_id :
    (etaleAssociatedVaryingSystemPullback (𝟙 X) R Y hY).hom =
      Functor.whiskerLeft (etaleAssociatedVaryingSystemFunctor (R := R) X Y hY)
          (etaleSheafDiagramRestrictionId (I := I) R X).hom ≫
        (Functor.rightUnitor _).hom ≫
        etaleAssociatedVaryingSystemCoverChange X R
          (etaleTorsorDiagramPullback_isFiniteGeometricTorsor (𝟙 X) D Y hY) hY
          ((etaleTorsorDiagramPullbackId D).hom.app Y) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext i
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, NatTrans.id_app,
    etaleAssociatedVaryingSystemPullback_hom_app,
    etaleSheafDiagramRestrictionId_hom_app_app,
    etaleAssociatedVaryingSystemCoverChange_app,
    etaleTorsorDiagramPullbackId_evaluation]
  exact etaleConstantAssociatedPullback_id R (Y.action i) (M.action i)

/-- The single system comparison agrees with successive comparisons followed
by contravariant change along the actual single-to-iterated cover map. -/
@[reassoc] theorem etaleAssociatedVaryingSystemPullback_comp :
    (etaleAssociatedVaryingSystemPullbackComp f g R Y hY).hom =
      Functor.whiskerRight (etaleAssociatedVaryingSystemPullback f R Y hY).hom
          ((Functor.whiskeringRight I _ _).obj
            (EtalePullback.restriction g (ModuleCat.{u} R))) ≫
        (etaleAssociatedVaryingSystemPullback g R
          ((etaleTorsorDiagramPullback f D).obj Y)
          (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY)).hom ≫
        etaleAssociatedVaryingSystemCoverChange W R
          (etaleTorsorDiagramPullback_isFiniteGeometricTorsor (g ≫ f) D Y hY)
          (etaleTorsorDiagramPullback_isFiniteGeometricTorsor g D
            ((etaleTorsorDiagramPullback f D).obj Y)
            (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY))
          ((etaleTorsorDiagramPullbackComp f D g).hom.app Y) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext i
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskeringRight_obj_map,
    etaleAssociatedVaryingSystemPullbackComp_hom_app_app,
    etaleAssociatedVaryingSystemPullback_hom_app,
    etaleAssociatedVaryingSystemCoverChange_app,
    etaleTorsorDiagramPullbackComp_evaluation]
  exact etaleConstantAssociatedPullback_comp f g R (Y.action i) (M.action i)

end Langlands.Shimura.Coefficients

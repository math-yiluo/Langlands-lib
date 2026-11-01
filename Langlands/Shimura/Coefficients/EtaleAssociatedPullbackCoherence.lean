import Langlands.Shimura.Coefficients.EtaleProductPullbackCoherence

/-! # Unit and composition coherence of associated coefficient-sheaf base change -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z W : Scheme.{u}}
variable (f : Z ⟶ X) [Etale f] (g : W ⟶ Z) [Etale g]
variable (R : Type u) [CommRing R]

/-- Identity restriction identifies the whole sheaf-valued coefficient action. -/
def etaleCoefficientRestrictionId (X : Scheme.{u}) (G : Type u) [Group G] :
    (EtalePullback.restriction (𝟙 X) (ModuleCat.{u} R)).mapAction G ≅
      𝟭 (Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :=
  Functor.mapActionCongr G (EtalePullback.restrictionId (ModuleCat.{u} R))

/-- Composition restriction identifies the whole sheaf-valued coefficient action. -/
def etaleCoefficientRestrictionComp (G : Type u) [Group G] :
    (EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G ⋙
        (EtalePullback.restriction g (ModuleCat.{u} R)).mapAction G ≅
      (EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)).mapAction G :=
  (Functor.mapActionComp G (EtalePullback.restriction f (ModuleCat.{u} R))
      (EtalePullback.restriction g (ModuleCat.{u} R))).symm ≪≫
    Functor.mapActionCongr G (EtalePullback.restrictionComp f (ModuleCat.{u} R) g)

/-- The identity coefficient comparison is the original restriction map. -/
@[simp] theorem etaleCoefficientRestrictionId_hom_app_hom
    (X : Scheme.{u}) (G : Type u) [Group G]
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    ((etaleCoefficientRestrictionId R X G).hom.app F).hom =
      (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app F.V := rfl

/-- The coefficient composition comparison is the original restriction map. -/
@[simp] theorem etaleCoefficientRestrictionComp_hom_app_hom
    (G : Type u) [Group G]
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    ((etaleCoefficientRestrictionComp f g R G).hom.app F).hom =
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app F.V := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

variable {G : Type u} [Group G] (Y : Action X.Etale G)

/-- The natural two-step restriction comparison with the associated sheaf for
single geometric base change at the target. -/
def etaleAssociatedPullbackComp :
    (associatedFunctor (R := R) X.smallEtaleTopology Y ⋙
        EtalePullback.restriction f (ModuleCat.{u} R)) ⋙
      EtalePullback.restriction g (ModuleCat.{u} R) ≅
    (EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)).mapAction G ⋙
      associatedFunctor W.smallEtaleTopology
        ((etaleTorsorPullbackFunctor (g ≫ f) G).obj Y) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (associatedFunctor (R := R) X.smallEtaleTopology Y)
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g) ≪≫
    etaleAssociatedPullback (g ≫ f) R Y

/-- The two-step associated-sheaf comparison uses restriction composition. -/
@[simp] theorem etaleAssociatedPullbackComp_hom_app
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (etaleAssociatedPullbackComp f g R Y).hom.app F =
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app
        (associated X.smallEtaleTopology Y F) ≫
      (etaleAssociatedPullback (g ≫ f) R Y).hom.app F := by
  change 𝟙 _ ≫ _ ≫ _ = _
  exact Category.id_comp _

/-- Identity restriction gives the associated cover map along the actual
first-projection comparison, after identifying the coefficient action. -/
@[reassoc] theorem etaleAssociatedPullback_id
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (etaleAssociatedPullback (𝟙 X) R Y).hom.app F ≫
      (associatedFunctor (R := R) X.smallEtaleTopology
        ((etaleTorsorPullbackFunctor (𝟙 X) G).obj Y)).map
          (X := ((EtalePullback.restriction (𝟙 X) (ModuleCat.{u} R)).mapAction G).obj F)
          (Y := F)
          ((etaleCoefficientRestrictionId R X G).hom.app F) =
    (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app
        (associated X.smallEtaleTopology Y F) ≫
      crossCoverMap X.smallEtaleTopology (MonoidHom.id G)
        ((etaleTorsorPullbackId X G).hom.app Y) (𝟙 F) := by
  apply hom_ext X.smallEtaleTopology
    ((etaleTorsorPullbackFunctor (𝟙 X) G).obj Y)
  rw [Category.assoc, inclusion_natural]
  simp only [Category.assoc, crossCoverMap_inclusion,
    etaleAssociatedPullback_hom_inclusion_assoc]
  change (EtalePullback.restriction (𝟙 X) (ModuleCat.{u} R)).map
      (inclusion X.smallEtaleTopology Y F) ≫
      (etaleProductSheafPullback (𝟙 X) R Y.V).hom.app F.V ≫
      (productSheaf X.smallEtaleTopology
        ((etaleObjectPullback (𝟙 X)).obj Y.V)).map
          ((EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app F.V) =
    (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app
      (associated X.smallEtaleTopology Y F) ≫
      inclusion X.smallEtaleTopology Y F ≫
      coverPullback X.smallEtaleTopology ((etaleObjectPullbackId X).hom.app Y.V) F.V ≫
      (productSheaf X.smallEtaleTopology
        ((etaleObjectPullback (𝟙 X)).obj Y.V)).map (𝟙 F.V)
  rw [etaleProductSheafPullback_id]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id, ← Category.assoc,
    (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.naturality]
  rfl

/-- Successive associated-sheaf comparisons agree with the single comparison,
including coefficient identification and contravariant geometric cover change. -/
@[reassoc] theorem etaleAssociatedPullback_comp
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app
        (associated X.smallEtaleTopology Y F) ≫
      (etaleAssociatedPullback (g ≫ f) R Y).hom.app F =
    (EtalePullback.restriction g (ModuleCat.{u} R)).map
        ((etaleAssociatedPullback f R Y).hom.app F) ≫
      (etaleAssociatedPullback g R ((etaleTorsorPullbackFunctor f G).obj Y)).hom.app
        (((EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G).obj F) ≫
      (associatedFunctor (R := R) W.smallEtaleTopology
        ((etaleTorsorPullbackFunctor g G).obj
          ((etaleTorsorPullbackFunctor f G).obj Y))).map
        ((etaleCoefficientRestrictionComp f g R G).hom.app F) ≫
      crossCoverMap W.smallEtaleTopology (MonoidHom.id G)
        ((etaleTorsorPullbackComp f G g).hom.app Y)
        (𝟙 (((EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)).mapAction G).obj F)) := by
  apply hom_ext W.smallEtaleTopology
    ((etaleTorsorPullbackFunctor (g ≫ f) G).obj Y)
  simp only [Category.assoc, crossCoverMap_inclusion,
    etaleAssociatedPullback_hom_inclusion]
  rw [inclusion_natural_assoc]
  simp only [Action.id_hom, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [etaleAssociatedPullback_hom_inclusion_assoc,
    ← CategoryTheory.Functor.map_comp_assoc,
    etaleAssociatedPullback_hom_inclusion,
    CategoryTheory.Functor.map_comp]
  simp only [etaleCoefficientRestrictionComp_hom_app_hom]
  simp only [Category.assoc]
  change (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app
      (associated X.smallEtaleTopology Y F) ≫
      (EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)).map
        (inclusion X.smallEtaleTopology Y F) ≫
      (etaleProductSheafPullback (g ≫ f) R Y.V).hom.app F.V =
    (EtalePullback.restriction g (ModuleCat.{u} R)).map
      ((EtalePullback.restriction f (ModuleCat.{u} R)).map
        (inclusion X.smallEtaleTopology Y F)) ≫
      (EtalePullback.restriction g (ModuleCat.{u} R)).map
        ((etaleProductSheafPullback f R Y.V).hom.app F.V) ≫
      (etaleProductSheafPullback g R ((etaleObjectPullback f).obj Y.V)).hom.app
        ((EtalePullback.restriction f (ModuleCat.{u} R)).obj F.V) ≫
      (productSheaf W.smallEtaleTopology
        ((etaleObjectPullback g).obj ((etaleObjectPullback f).obj Y.V))).map
          ((EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app F.V) ≫
      coverPullback W.smallEtaleTopology
        ((MorphismProperty.Over.pullbackComp g f).hom.app Y.V)
          ((EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)).obj F.V)
  rw [← Category.assoc,
    ← (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [etaleProductSheafPullback_comp]

end Langlands.Shimura.Coefficients

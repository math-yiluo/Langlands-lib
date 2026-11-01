import Langlands.Shimura.Coefficients.EtaleAssociatedPullbackCoherence
import Langlands.Shimura.Coefficients.EtaleConstantAssociatedPullback
import Langlands.Shimura.Coefficients.EtaleCrossCover

/-! # Coherence of constant-module associated-sheaf base change -/

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
variable {G : Type u} [Group G]

/-- The constant-action comparison at the identity is coefficient restriction identity. -/
@[simp] theorem etaleConstantActionPullback_id (X : Scheme.{u})
    (M : Action (ModuleCat.{u} R) G) :
    (etaleConstantActionPullback (𝟙 X) R).hom.app M =
      (etaleCoefficientRestrictionId R X G).hom.app
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) := by
  apply Action.Hom.ext
  simpa only [etaleConstantActionPullback_hom_hom,
    etaleCoefficientRestrictionId_hom_app_hom, Functor.mapAction_obj_V] using
      EtalePullback.constantPullbackIso_id (X := X) (ModuleCat.{u} R) M.V

/-- Successive constant-action comparisons agree with restriction composition. -/
@[reassoc] theorem etaleConstantActionPullback_comp (M : Action (ModuleCat.{u} R) G) :
    (etaleCoefficientRestrictionComp f g R G).hom.app
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
      (etaleConstantActionPullback (g ≫ f) R).hom.app M =
    ((EtalePullback.restriction g (ModuleCat.{u} R)).mapAction G).map
        ((etaleConstantActionPullback f R).hom.app M) ≫
      (etaleConstantActionPullback g R).hom.app M := by
  apply Action.Hom.ext
  simpa only [Action.comp_hom, etaleConstantActionPullback_hom_hom,
    etaleCoefficientRestrictionComp_hom_app_hom, Functor.mapAction_obj_V,
    Functor.mapAction_map_hom] using
      EtalePullback.constantPullbackIso_comp f (ModuleCat.{u} R) g M.V

variable (Y : Action X.Etale G)

/-- The constant comparison applies associated base change and then identifies
its entire restricted coefficient action. -/
@[simp] theorem etaleConstantAssociatedPullback_hom_app
    (M : Action (ModuleCat.{u} R) G) :
    (etaleConstantAssociatedPullback f R Y).hom.app M =
      (etaleAssociatedPullback f R Y).hom.app
        (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
      (associatedFunctor (R := R) Z.smallEtaleTopology
        ((etaleTorsorPullbackFunctor f G).obj Y)).map
        (X := ((EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G).obj
          (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M))
        (Y := ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)
        ((etaleConstantActionPullback f R).hom.app M) := rfl

/-- Two restrictions of a constant-module associated sheaf compare naturally
with the associated sheaf on the actual single-pullback cover. -/
def etaleConstantAssociatedPullbackComp :
    (etaleAssociatedFunctor (R := R) X Y ⋙
        EtalePullback.restriction f (ModuleCat.{u} R)) ⋙
      EtalePullback.restriction g (ModuleCat.{u} R) ≅
    etaleAssociatedFunctor W ((etaleTorsorPullbackFunctor (g ≫ f) G).obj Y) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleAssociatedFunctor (R := R) X Y)
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g) ≪≫
    etaleConstantAssociatedPullback (g ≫ f) R Y

/-- The two-step comparison has the canonical restriction-composition component. -/
@[simp] theorem etaleConstantAssociatedPullbackComp_hom_app
    (M : Action (ModuleCat.{u} R) G) :
    (etaleConstantAssociatedPullbackComp f g R Y).hom.app M =
      (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app
        ((etaleAssociatedFunctor X Y).obj M) ≫
      (etaleConstantAssociatedPullback (g ≫ f) R Y).hom.app M := by
  change 𝟙 _ ≫ _ ≫ _ = _
  exact Category.id_comp _

/-- Identity restriction is the constant-associated cover map along the actual
first projection of the identity fiber product. -/
@[reassoc] theorem etaleConstantAssociatedPullback_id
    (M : Action (ModuleCat.{u} R) G) :
    (etaleConstantAssociatedPullback (𝟙 X) R Y).hom.app M =
      (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app
          ((etaleAssociatedFunctor X Y).obj M) ≫
        etaleCrossCoverMap X (MonoidHom.id G)
          ((etaleTorsorPullbackId X G).hom.app Y) (𝟙 M) := by
  change (etaleAssociatedPullback (𝟙 X) R Y).hom.app
      (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
    (associatedFunctor (R := R) X.smallEtaleTopology
      ((etaleTorsorPullbackFunctor (𝟙 X) G).obj Y)).map
        (X := ((EtalePullback.restriction (𝟙 X) (ModuleCat.{u} R)).mapAction G).obj
          (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M))
        (Y := ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)
        ((etaleConstantActionPullback (𝟙 X) R).hom.app M) = _
  rw [etaleConstantActionPullback_id, etaleAssociatedPullback_id]
  dsimp only [etaleCrossCoverMap, constantCrossCoverMap]
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- Successive constant-associated comparisons agree with the single
comparison, retaining contravariant change along the actual geometric cover. -/
@[reassoc] theorem etaleConstantAssociatedPullback_comp
    (M : Action (ModuleCat.{u} R) G) :
    (EtalePullback.restrictionComp f (ModuleCat.{u} R) g).hom.app
        ((etaleAssociatedFunctor X Y).obj M) ≫
      (etaleConstantAssociatedPullback (g ≫ f) R Y).hom.app M =
    (EtalePullback.restriction g (ModuleCat.{u} R)).map
        ((etaleConstantAssociatedPullback f R Y).hom.app M) ≫
      (etaleConstantAssociatedPullback g R
        ((etaleTorsorPullbackFunctor f G).obj Y)).hom.app M ≫
      etaleCrossCoverMap W (MonoidHom.id G)
        ((etaleTorsorPullbackComp f G g).hom.app Y) (𝟙 M) := by
  let F := ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M
  let A := associatedFunctor (R := R) W.smallEtaleTopology
    ((etaleTorsorPullbackFunctor g G).obj ((etaleTorsorPullbackFunctor f G).obj Y))
  let B := associatedFunctor (R := R) W.smallEtaleTopology
    ((etaleTorsorPullbackFunctor (g ≫ f) G).obj Y)
  let a := (etaleTorsorPullbackComp f G g).hom.app Y
  let c := (etaleConstantActionPullback (g ≫ f) R).hom.app M
  have hn :
      crossCoverMap W.smallEtaleTopology (MonoidHom.id G) a
          (𝟙 (((EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)).mapAction G).obj F)) ≫
        B.map c =
      A.map c ≫ crossCoverMap W.smallEtaleTopology (MonoidHom.id G) a
        (𝟙 (((constantSheaf W.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)) := by
    dsimp only [A, B]
    apply hom_ext W.smallEtaleTopology
      ((etaleTorsorPullbackFunctor (g ≫ f) G).obj Y)
    rw [Category.assoc, inclusion_natural]
    simp only [Category.assoc, crossCoverMap_inclusion, crossCoverMap_inclusion_assoc,
      inclusion_natural_assoc, Action.id_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    exact congrArg (fun k => inclusion W.smallEtaleTopology
      ((etaleTorsorPullbackFunctor g G).obj ((etaleTorsorPullbackFunctor f G).obj Y))
      (((EtalePullback.restriction (g ≫ f) (ModuleCat.{u} R)).mapAction G).obj F) ≫ k)
      (coverPullback_natural W.smallEtaleTopology a.hom c.hom)
  simp only [etaleConstantAssociatedPullback_hom_app, CategoryTheory.Functor.map_comp,
    Category.assoc]
  erw [etaleAssociatedPullback_comp_assoc f g R Y F]
  erw [hn]
  rw [← CategoryTheory.Functor.map_comp_assoc, etaleConstantActionPullback_comp]
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [← (etaleAssociatedPullback g R
    ((etaleTorsorPullbackFunctor f G).obj Y)).hom.naturality_assoc
      ((etaleConstantActionPullback f R).hom.app M)]
  dsimp only [etaleCrossCoverMap, constantCrossCoverMap]
  erw [CategoryTheory.Functor.map_id]
  rfl

end Langlands.Shimura.Coefficients

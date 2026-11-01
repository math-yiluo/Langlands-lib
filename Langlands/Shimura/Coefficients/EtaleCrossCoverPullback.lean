import Langlands.Shimura.Coefficients.EtaleConstantAssociatedPullback
import Langlands.Shimura.Coefficients.EtaleCrossCover
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Cross-cover coefficient maps and actual etale restriction -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]

/-- The product-sheaf comparison is compatible with every cover morphism. -/
@[reassoc] theorem etaleProductSheafPullback_cover
    {V V' : X.Etale} (a : V' ⟶ V)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (EtalePullback.restriction f (ModuleCat.{u} R)).map
        (coverPullback X.smallEtaleTopology a F) ≫
        (etaleProductSheafPullback f R V').hom.app F =
      (etaleProductSheafPullback f R V).hom.app F ≫
        coverPullback Z.smallEtaleTopology ((etaleObjectPullback f).map a)
          ((EtalePullback.restriction f (ModuleCat.{u} R)).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (prod.map a (𝟙 ((EtalePullback.siteMap f).obj U.unop))).op ≫
      F.obj.map (etaleProductPullbackHom f V' U.unop).op =
    F.obj.map (etaleProductPullbackHom f V U.unop).op ≫
      F.obj.map ((EtalePullback.siteMap f).map
        (prod.map ((etaleObjectPullback f).map a) (𝟙 U.unop))).op
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  have h := etaleProductPullbackHom_natural f a (𝟙 U.unop)
  erw [CategoryTheory.Functor.map_id] at h
  exact h.symm

variable {G H : Type u} [Group G] [Group H]
variable {Y : Action X.Etale G} {Y' : Action X.Etale H}
variable (φ : H →* G) (a : Y' ⟶ (Action.res X.Etale φ).obj Y)
variable {F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G}
variable {E : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) H}

/-- Etale restriction commutes with simultaneous cover, group and coefficient change. -/
@[reassoc] theorem etaleAssociatedPullback_crossCover
    (c : (Action.res (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) φ).obj F ⟶ E) :
    (EtalePullback.restriction f (ModuleCat.{u} R)).map
        (crossCoverMap X.smallEtaleTopology φ a c) ≫
        (etaleAssociatedPullback f R Y').hom.app E =
      (etaleAssociatedPullback f R Y).hom.app F ≫
        crossCoverMap Z.smallEtaleTopology φ
          ((etaleTorsorPullbackFunctor f H).map a)
          (((EtalePullback.restriction f (ModuleCat.{u} R)).mapAction H).map c) := by
  apply hom_ext Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f H).obj Y')
  rw [Category.assoc, etaleAssociatedPullback_hom_inclusion,
    ← CategoryTheory.Functor.map_comp_assoc, crossCoverMap_inclusion,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rw [Category.assoc, Category.assoc]
  erw [(etaleProductSheafPullback f R Y'.V).hom.naturality c.hom]
  simp only [Category.assoc, crossCoverMap_inclusion,
    etaleAssociatedPullback_hom_inclusion_assoc]
  erw [etaleProductSheafPullback_cover_assoc]
  rfl

/-- The comparison identifies the complete cross-cover arrow, including both
its source and target associated sheaves. -/
@[simps! hom_left hom_right inv_left inv_right]
def etaleCrossCoverPullbackIso
    (c : (Action.res (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) φ).obj F ⟶ E) :
    Arrow.mk ((EtalePullback.restriction f (ModuleCat.{u} R)).map
        (crossCoverMap X.smallEtaleTopology φ a c)) ≅
      Arrow.mk (crossCoverMap Z.smallEtaleTopology
        (Y := (etaleTorsorPullbackFunctor f G).obj Y)
        (Z := (etaleTorsorPullbackFunctor f H).obj Y') φ
        ((etaleTorsorPullbackFunctor f H).map a)
        (F := ((EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G).obj F)
        (E := ((EtalePullback.restriction f (ModuleCat.{u} R)).mapAction H).obj E)
        (((EtalePullback.restriction f (ModuleCat.{u} R)).mapAction H).map c)) :=
  Arrow.isoMk ((etaleAssociatedPullback f R Y).app F)
    ((etaleAssociatedPullback f R Y').app E)
    (etaleAssociatedPullback_crossCover f R φ a c).symm

/-- The constant-module comparison respects every compatible cover and
coefficient map, including changes of deck group. -/
@[reassoc] theorem etaleConstantAssociatedPullback_crossCover
    {M : Action (ModuleCat.{u} R) G} {N : Action (ModuleCat.{u} R) H}
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (EtalePullback.restriction f (ModuleCat.{u} R)).map
        (etaleCrossCoverMap X φ a c) ≫
        (etaleConstantAssociatedPullback f R Y').hom.app N =
      (etaleConstantAssociatedPullback f R Y).hom.app M ≫
        etaleCrossCoverMap Z φ ((etaleTorsorPullbackFunctor f H).map a) c := by
  dsimp only [etaleCrossCoverMap, constantCrossCoverMap]
  apply hom_ext Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f H).obj Y')
  rw [Category.assoc, etaleConstantAssociatedPullback_hom_inclusion,
    ← CategoryTheory.Functor.map_comp_assoc]
  erw [crossCoverMap_inclusion]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [(etaleProductSheafPullback f R Y'.V).hom.naturality_assoc
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map c.hom)]
  erw [etaleProductSheafPullback_cover_assoc f R a.hom
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V)]
  rw [crossCoverMap_inclusion]
  erw [etaleConstantAssociatedPullback_hom_inclusion_assoc f R Y M]
  simp only [etaleTorsorPullbackFunctor, Functor.mapAction_map_hom,
    Functor.mapAction_obj_V, Action.res_obj_V, Functor.comp_map]
  rw [← coverPullback_natural_assoc Z.smallEtaleTopology
    (Y := (etaleObjectPullback f).obj Y.V)
    (Z := (etaleObjectPullback f).obj Y'.V)
    ((etaleObjectPullback f).map a.hom)
    ((EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.app M.V)]
  simp only [← CategoryTheory.Functor.map_comp]
  erw [(EtalePullback.constantPullbackIso f (ModuleCat.{u} R)).hom.naturality c.hom]
  rfl

/-- Constant coefficients give the same isomorphism of actual geometric
cross-cover arrows. -/
@[simps! hom_left hom_right inv_left inv_right]
def etaleConstantCrossCoverPullbackIso
    {M : Action (ModuleCat.{u} R) G} {N : Action (ModuleCat.{u} R) H}
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    Arrow.mk ((EtalePullback.restriction f (ModuleCat.{u} R)).map
        (etaleCrossCoverMap X φ a c)) ≅
      Arrow.mk (etaleCrossCoverMap Z
        (Y := (etaleTorsorPullbackFunctor f G).obj Y)
        (Z := (etaleTorsorPullbackFunctor f H).obj Y') φ
        ((etaleTorsorPullbackFunctor f H).map a) c) :=
  Arrow.isoMk ((etaleConstantAssociatedPullback f R Y).app M)
    ((etaleConstantAssociatedPullback f R Y').app N)
    (etaleConstantAssociatedPullback_crossCover f R φ a c).symm

end Langlands.Shimura.Coefficients

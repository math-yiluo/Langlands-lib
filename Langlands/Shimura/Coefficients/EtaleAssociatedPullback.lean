import Langlands.Shimura.Coefficients.EtaleProductPullback
import Langlands.Geometry.EtalePullbackAdjunction

/-! # Etale restriction and actual associated coefficient sheaves -/

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

/-- Actual product sheaves commute with restriction along an etale morphism. -/
def etaleProductSheafPullback (V : X.Etale) :
    productSheaf X.smallEtaleTopology V ⋙ EtalePullback.restriction f (ModuleCat.{u} R) ≅
      EtalePullback.restriction f (ModuleCat.{u} R) ⋙
        productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _
      (NatIso.ofComponents
        (fun U => F.obj.mapIso (etaleProductPullbackIso f V U.unop).op)
        (fun {U U'} b => by
          change F.obj.map (prod.map (𝟙 V) ((EtalePullback.siteMap f).map b.unop)).op ≫
              F.obj.map (etaleProductPullbackHom f V U'.unop).op =
            F.obj.map (etaleProductPullbackHom f V U.unop).op ≫
              F.obj.map ((EtalePullback.siteMap f).map
                (prod.map (𝟙 ((etaleObjectPullback f).obj V)) b.unop)).op
          rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
          congr 1
          apply Quiver.Hom.unop_inj
          have h := etaleProductPullbackHom_natural f (𝟙 V) b.unop
          erw [CategoryTheory.Functor.map_id] at h
          exact h.symm)))
    (fun {F F'} a => by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      exact (a.hom.naturality (etaleProductPullbackHom f V U.unop).op).symm)

/-- The product-sheaf comparison intertwines every deck endomorphism. -/
@[reassoc] theorem etaleProductSheafPullback_deck
    {V : X.Etale} (a : V ⟶ V) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (EtalePullback.restriction f (ModuleCat.{u} R)).map (deckMap X.smallEtaleTopology a F) ≫
        (etaleProductSheafPullback f R V).hom.app F =
      (etaleProductSheafPullback f R V).hom.app F ≫
        deckMap Z.smallEtaleTopology ((etaleObjectPullback f).map a)
          ((EtalePullback.restriction f (ModuleCat.{u} R)).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change F.obj.map (prod.map a (𝟙 ((EtalePullback.siteMap f).obj U.unop))).op ≫
      F.obj.map (etaleProductPullbackHom f V U.unop).op =
    F.obj.map (etaleProductPullbackHom f V U.unop).op ≫
      F.obj.map ((EtalePullback.siteMap f).map
        (prod.map ((etaleObjectPullback f).map a) (𝟙 U.unop))).op
  rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  have h := etaleProductPullbackHom_natural f a (𝟙 U.unop)
  erw [CategoryTheory.Functor.map_id] at h
  exact h.symm

variable {G : Type u} [Group G] (Y : Action X.Etale G)

local instance : HasLimitsOfShape (SingleObj G) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

local instance : PreservesLimitsOfShape (SingleObj G)
    (EtalePullback.restriction f (ModuleCat.{u} R)) :=
  (EtalePullback.extensionAdjunction f R).rightAdjoint_preservesLimits.preservesLimitsOfShape

/-- Restriction identifies the actual diagonal action with that of the
base-changed cover and restricted coefficients. -/
def etaleDiagonalPullback :
    diagonalFunctor X.smallEtaleTopology Y ⋙
        (EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G ≅
      (EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G ⋙
        diagonalFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y) :=
  NatIso.ofComponents
    (fun F => Action.mkIso ((etaleProductSheafPullback f R Y.V).app F.V)
      (fun g => by
        change (EtalePullback.restriction f (ModuleCat.{u} R)).map
            (deckMap X.smallEtaleTopology (Y.ρ g⁻¹) F.V ≫
              (productSheaf X.smallEtaleTopology Y.V).map (F.ρ g)) ≫
            (etaleProductSheafPullback f R Y.V).hom.app F.V =
          (etaleProductSheafPullback f R Y.V).hom.app F.V ≫
            (deckMap Z.smallEtaleTopology ((etaleObjectPullback f).map (Y.ρ g⁻¹))
                ((EtalePullback.restriction f (ModuleCat.{u} R)).obj F.V) ≫
              (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj Y.V)).map
                ((EtalePullback.restriction f (ModuleCat.{u} R)).map (F.ρ g)))
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
        erw [(etaleProductSheafPullback f R Y.V).hom.naturality (F.ρ g)]
        rw [← Category.assoc, etaleProductSheafPullback_deck, Category.assoc]
        rfl))
    (fun {F F'} a => by
      apply Action.hom_injective
      exact (etaleProductSheafPullback f R Y.V).hom.naturality a.hom)

/-- The complete invariant diagrams agree after etale restriction. -/
def etaleInvariantDiagramPullback :
    invariantDiagram X.smallEtaleTopology Y ⋙
        (Functor.whiskeringRight (SingleObj G) _ _).obj
          (EtalePullback.restriction f (ModuleCat.{u} R)) ≅
      (EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G ⋙
        invariantDiagram Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y) :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun _ => (etaleProductSheafPullback f R Y.V).app F.V)
      (fun {i j} g => ((etaleDiagonalPullback f R Y).hom.app F).comm g))
    (fun {F F'} a => by
      apply NatTrans.ext
      funext j
      exact (etaleProductSheafPullback f R Y.V).hom.naturality a.hom)

/-- Actual associated sheaves commute with etale restriction, naturally in
arbitrary sheaf-valued coefficient representations. -/
def etaleAssociatedPullback :
    associatedFunctor X.smallEtaleTopology Y ⋙
        EtalePullback.restriction f (ModuleCat.{u} R) ≅
      (EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G ⋙
        associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y) :=
  Functor.isoWhiskerLeft (invariantDiagram X.smallEtaleTopology Y)
      (preservesLimitNatIso (EtalePullback.restriction f (ModuleCat.{u} R))) ≪≫
    Functor.isoWhiskerRight (etaleInvariantDiagramPullback f R Y) lim

/-- The associated-sheaf comparison has the expected map on invariant sections. -/
@[reassoc (attr := simp)] theorem etaleAssociatedPullback_hom_inclusion
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (etaleAssociatedPullback f R Y).hom.app F ≫
        inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G).obj F) =
      (EtalePullback.restriction f (ModuleCat.{u} R)).map
          (inclusion X.smallEtaleTopology Y F) ≫
        (etaleProductSheafPullback f R Y.V).hom.app F.V := by
  change (preservesLimitIso _ _).hom ≫
      lim.map ((etaleInvariantDiagramPullback f R Y).hom.app F) ≫
      limit.π _ (SingleObj.star G) = _
  erw [limMap_π]
  rw [← Category.assoc, preservesLimitIso_hom_π]
  rfl

/-- The inverse comparison recovers the original inclusion after restriction. -/
@[reassoc (attr := simp)] theorem etaleAssociatedPullback_inv_inclusion
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (etaleAssociatedPullback f R Y).inv.app F ≫
        (EtalePullback.restriction f (ModuleCat.{u} R)).map
          (inclusion X.smallEtaleTopology Y F) =
      inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((EtalePullback.restriction f (ModuleCat.{u} R)).mapAction G).obj F) ≫
        (etaleProductSheafPullback f R Y.V).inv.app F.V := by
  apply (cancel_mono ((etaleProductSheafPullback f R Y.V).hom.app F.V)).1
  rw [Category.assoc, ← etaleAssociatedPullback_hom_inclusion,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end Langlands.Shimura.Coefficients

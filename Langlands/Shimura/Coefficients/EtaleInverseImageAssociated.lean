import Langlands.Geometry.EtaleInverseImageExact
import Langlands.Shimura.Coefficients.Etale
import Langlands.Shimura.Coefficients.CrossCover
import Mathlib.Basic.Countable.Small

/-! # Inverse image of associated coefficient sheaves along arbitrary morphisms -/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtaleDirectImage Langlands.Geometry.EtaleInverseImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]

/-- Direct image commutes with product sheaves: both evaluate a sheaf on `Z` on the geometric
base change of `V × U`, identified with the product of base changes. -/
def directImageProductSheafIso (V : X.Etale) :
    directImage f (ModuleCat.{u} R) ⋙ productSheaf X.smallEtaleTopology V ≅
      productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V) ⋙
        directImage f (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _
      (NatIso.ofComponents
        (fun U => F.obj.mapIso (asIso (prodComparison (etaleObjectPullback f) V U.unop)).symm.op)
        (fun {U U'} b => by
          change F.obj.map ((etaleObjectPullback f).map (prod.map (𝟙 V) b.unop)).op ≫
              F.obj.map (inv (prodComparison (etaleObjectPullback f) V U'.unop)).op =
            F.obj.map (inv (prodComparison (etaleObjectPullback f) V U.unop)).op ≫
              F.obj.map (prod.map (𝟙 ((etaleObjectPullback f).obj V))
                ((etaleObjectPullback f).map b.unop)).op
          rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp,
            prodComparison_inv_natural, CategoryTheory.Functor.map_id])))
    (fun {F F'} a => by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      exact (a.hom.naturality _).symm)

/-- The direct-image comparison intertwines deck endomorphisms of the cover. -/
@[reassoc] theorem directImageProductSheafIso_deck {V : X.Etale} (a : V ⟶ V)
    (H : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) :
    deckMap X.smallEtaleTopology a ((directImage f (ModuleCat.{u} R)).obj H) ≫
        (directImageProductSheafIso f R V).hom.app H =
      (directImageProductSheafIso f R V).hom.app H ≫
        (directImage f (ModuleCat.{u} R)).map
          (deckMap Z.smallEtaleTopology ((etaleObjectPullback f).map a) H) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change H.obj.map ((etaleObjectPullback f).map (prod.map a (𝟙 U.unop))).op ≫
      H.obj.map (inv (prodComparison (etaleObjectPullback f) V U.unop)).op =
    H.obj.map (inv (prodComparison (etaleObjectPullback f) V U.unop)).op ≫
      H.obj.map (prod.map ((etaleObjectPullback f).map a)
        (𝟙 ((etaleObjectPullback f).obj U.unop))).op
  rw [← H.obj.map_comp, ← H.obj.map_comp, ← op_comp, ← op_comp,
    prodComparison_inv_natural, CategoryTheory.Functor.map_id]

/-- The direct-image comparison intertwines restriction along any map of cover objects. -/
@[reassoc] theorem directImageProductSheafIso_coverPullback {V V' : X.Etale} (a : V' ⟶ V)
    (H : Sheaf Z.smallEtaleTopology (ModuleCat.{u} R)) :
    coverPullback X.smallEtaleTopology a ((directImage f (ModuleCat.{u} R)).obj H) ≫
        (directImageProductSheafIso f R V').hom.app H =
      (directImageProductSheafIso f R V).hom.app H ≫
        (directImage f (ModuleCat.{u} R)).map
          (coverPullback Z.smallEtaleTopology ((etaleObjectPullback f).map a) H) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change H.obj.map ((etaleObjectPullback f).map (prod.map a (𝟙 U.unop))).op ≫
      H.obj.map (inv (prodComparison (etaleObjectPullback f) V' U.unop)).op =
    H.obj.map (inv (prodComparison (etaleObjectPullback f) V U.unop)).op ≫
      H.obj.map (prod.map ((etaleObjectPullback f).map a)
        (𝟙 ((etaleObjectPullback f).obj U.unop))).op
  rw [← H.obj.map_comp, ← H.obj.map_comp, ← op_comp, ← op_comp,
    prodComparison_inv_natural, CategoryTheory.Functor.map_id]

/-- The base-change map from the inverse image of a product sheaf to the product sheaf of
the inverse image: the adjoint of the inverse-image unit followed by the direct-image
comparison. -/
def inverseImageProductSheafMap (V : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImage f R).obj ((productSheaf X.smallEtaleTopology V).obj F) ⟶
      (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V)).obj
        ((inverseImage f R).obj F) :=
  ((inverseImageAdjunction f R).homEquiv _ _).symm
    ((productSheaf X.smallEtaleTopology V).map ((inverseImageAdjunction f R).unit.app F) ≫
      (directImageProductSheafIso f R V).hom.app ((inverseImage f R).obj F))

/-- The adjoint of the base-change map is the unit followed by the direct-image comparison. -/
theorem homEquiv_inverseImageProductSheafMap (V : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImageAdjunction f R).homEquiv _ _ (inverseImageProductSheafMap f R V F) =
      (productSheaf X.smallEtaleTopology V).map ((inverseImageAdjunction f R).unit.app F) ≫
        (directImageProductSheafIso f R V).hom.app ((inverseImage f R).obj F) :=
  Equiv.apply_symm_apply _ _

/-- The base-change map is natural in the coefficient sheaf. -/
@[reassoc] theorem inverseImageProductSheafMap_natural (V : X.Etale)
    {F F' : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)} (a : F ⟶ F') :
    (inverseImage f R).map ((productSheaf X.smallEtaleTopology V).map a) ≫
        inverseImageProductSheafMap f R V F' =
      inverseImageProductSheafMap f R V F ≫
        (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V)).map
          ((inverseImage f R).map a) := by
  apply ((inverseImageAdjunction f R).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_inverseImageProductSheafMap, homEquiv_inverseImageProductSheafMap]
  have h1 := (directImageProductSheafIso f R V).hom.naturality ((inverseImage f R).map a)
  have h2 := (inverseImageAdjunction f R).unit.naturality a
  simp only [Functor.comp_map, Functor.id_map] at h1 h2
  rw [← Functor.map_comp_assoc, h2, Functor.map_comp, Category.assoc, h1, Category.assoc]

/-- The base-change map as a natural transformation. -/
def inverseImageProductSheafNatTrans (V : X.Etale) :
    productSheaf X.smallEtaleTopology V ⋙ inverseImage f R ⟶
      inverseImage f R ⋙ productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj V) where
  app F := inverseImageProductSheafMap f R V F
  naturality _ _ a := inverseImageProductSheafMap_natural f R V a

/-- The base-change map intertwines every deck endomorphism. -/
@[reassoc] theorem inverseImageProductSheafMap_deck {V : X.Etale} (a : V ⟶ V)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImage f R).map (deckMap X.smallEtaleTopology a F) ≫
        inverseImageProductSheafMap f R V F =
      inverseImageProductSheafMap f R V F ≫
        deckMap Z.smallEtaleTopology ((etaleObjectPullback f).map a) ((inverseImage f R).obj F) := by
  apply ((inverseImageAdjunction f R).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_inverseImageProductSheafMap, deckMap_natural_assoc]
  erw [directImageProductSheafIso_deck]
  rw [Category.assoc]

/-- The base-change map is natural in the cover object: it intertwines restriction along any
map of cover objects with restriction along its geometric base change. -/
@[reassoc] theorem inverseImageProductSheafMap_coverPullback {V V' : X.Etale} (a : V' ⟶ V)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :
    (inverseImage f R).map (coverPullback X.smallEtaleTopology a F) ≫
        inverseImageProductSheafMap f R V' F =
      inverseImageProductSheafMap f R V F ≫
        coverPullback Z.smallEtaleTopology ((etaleObjectPullback f).map a)
          ((inverseImage f R).obj F) := by
  apply ((inverseImageAdjunction f R).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_inverseImageProductSheafMap, homEquiv_inverseImageProductSheafMap,
    coverPullback_natural_assoc]
  erw [directImageProductSheafIso_coverPullback]
  rw [Category.assoc]

variable {G : Type u} [Group G] (Y : Action X.Etale G)

local instance : HasLimitsOfShape (SingleObj G) (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfShape

/-- On diagonal actions, the base-change map is equivariant: the deck action on the base-changed
cover is the base change of the original deck action. -/
def inverseImageDiagonalMap (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    ((inverseImage f R).mapAction G).obj ((diagonalFunctor X.smallEtaleTopology Y).obj F) ⟶
      (diagonalFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)).obj
        (((inverseImage f R).mapAction G).obj F) where
  hom := inverseImageProductSheafMap f R Y.V F.V
  comm g := by
    change (inverseImage f R).map
        (deckMap X.smallEtaleTopology (Y.ρ g⁻¹) F.V ≫
          (productSheaf X.smallEtaleTopology Y.V).map (F.ρ g)) ≫
        inverseImageProductSheafMap f R Y.V F.V =
      inverseImageProductSheafMap f R Y.V F.V ≫
        (deckMap Z.smallEtaleTopology ((etaleObjectPullback f).map (Y.ρ g⁻¹))
            ((inverseImage f R).obj F.V) ≫
          (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj Y.V)).map
            ((inverseImage f R).map (F.ρ g)))
    rw [CategoryTheory.Functor.map_comp, Category.assoc, inverseImageProductSheafMap_natural,
      inverseImageProductSheafMap_deck_assoc]

/-- The equivariant base-change maps are natural in the coefficient action. -/
def inverseImageDiagonalNatTrans :
    diagonalFunctor X.smallEtaleTopology Y ⋙ (inverseImage f R).mapAction G ⟶
      (inverseImage f R).mapAction G ⋙
        diagonalFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y) where
  app F := inverseImageDiagonalMap f R Y F
  naturality _ _ a := by
    apply Action.hom_injective
    exact inverseImageProductSheafMap_natural f R Y.V a.hom

/-- The base-change map of the invariant diagrams. -/
def inverseImageInvariantMap (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (invariantDiagram X.smallEtaleTopology Y).obj F ⋙ inverseImage f R ⟶
      (invariantDiagram Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)).obj
        (((inverseImage f R).mapAction G).obj F) where
  app _ := inverseImageProductSheafMap f R Y.V F.V
  naturality _ _ g := (inverseImageDiagonalMap f R Y F).comm g

/-- The comparison from the inverse image of the associated sheaf to the associated sheaf of
the base-changed cover and the inverse-image coefficients: the inverse image of the limit maps
to the limit of inverse images, followed by the base-change maps of the invariant diagrams. -/
def inverseImageAssociatedMap :
    associatedFunctor X.smallEtaleTopology Y ⋙ inverseImage f R ⟶
      (inverseImage f R).mapAction G ⋙
        associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y) where
  app F := limit.post ((invariantDiagram X.smallEtaleTopology Y).obj F) (inverseImage f R) ≫
    limMap (inverseImageInvariantMap f R Y F)
  naturality {F F'} a := by
    apply limit.hom_ext
    intro j
    change (inverseImage f R).map (limMap ((invariantDiagram X.smallEtaleTopology Y).map a)) ≫
        (limit.post _ (inverseImage f R) ≫ limMap (inverseImageInvariantMap f R Y F')) ≫
          limit.π _ j =
      (limit.post _ (inverseImage f R) ≫ limMap (inverseImageInvariantMap f R Y F)) ≫
        limMap ((invariantDiagram Z.smallEtaleTopology
          ((etaleTorsorPullbackFunctor f G).obj Y)).map (((inverseImage f R).mapAction G).map a)) ≫
          limit.π _ j
    simp only [Category.assoc, limMap_π, limit.post_π_assoc, limMap_π_assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, limMap_π, CategoryTheory.Functor.map_comp,
      Category.assoc]
    exact congrArg ((inverseImage f R).map (limit.π _ j) ≫ ·)
      (inverseImageProductSheafMap_natural f R Y.V a.hom)

/-- The comparison has the base-change map on invariant sections. -/
@[reassoc] theorem inverseImageAssociatedMap_inclusion
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G) :
    (inverseImageAssociatedMap f R Y).app F ≫
        inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((inverseImage f R).mapAction G).obj F) =
      (inverseImage f R).map (inclusion X.smallEtaleTopology Y F) ≫
        inverseImageProductSheafMap f R Y.V F.V := by
  change (limit.post _ (inverseImage f R) ≫ limMap (inverseImageInvariantMap f R Y F)) ≫
      limit.π _ (SingleObj.star G) = _
  rw [Category.assoc, limMap_π, limit.post_π_assoc]
  rfl

section Finite

variable [Finite G]

local instance : Fintype (Shrink.{0} G) :=
  @Fintype.ofFinite _ (Finite.of_equiv G (equivShrink.{0} G))

/-- Inverse image preserves invariants under a finite group: the one-object category of the
group is equivalent to that of an isomorphic group in `Type`, which is finite. -/
instance inverseImage_preservesLimitsOfShape_singleObj :
    PreservesLimitsOfShape (SingleObj G) (inverseImage f R) :=
  preservesLimitsOfShape_of_equiv (Shrink.mulEquiv.{0} (α := G)).toSingleObjEquiv
    (inverseImage f R)

/-- For a finite group, the comparison of associated sheaves is an isomorphism wherever the
base-change map of the product sheaf is: inverse image preserves the finite invariant limit. -/
theorem isIso_inverseImageAssociatedMap_app
    (F : Action (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) G)
    [IsIso (inverseImageProductSheafMap f R Y.V F.V)] :
    IsIso ((inverseImageAssociatedMap f R Y).app F) := by
  have h0 : ∀ j, IsIso ((inverseImageInvariantMap f R Y F).app j) := fun _ =>
    inferInstanceAs (IsIso (inverseImageProductSheafMap f R Y.V F.V))
  have h1 : IsIso (limit.post ((invariantDiagram X.smallEtaleTopology Y).obj F)
    (inverseImage f R)) := inferInstance
  have h2 : IsIso (inverseImageInvariantMap f R Y F) := NatIso.isIso_of_isIso_app _
  have h3 : IsIso (limMap (inverseImageInvariantMap f R Y F)) := inferInstance
  change IsIso (limit.post ((invariantDiagram X.smallEtaleTopology Y).obj F) (inverseImage f R) ≫
    limMap (inverseImageInvariantMap f R Y F))
  exact IsIso.comp_isIso

end Finite

end Langlands.Shimura.Coefficients

import Langlands.Shimura.Coefficients.EtaleInverseImageAssociatedIso
import Langlands.Geometry.EtaleInverseImageConstant
import Langlands.Shimura.Coefficients.EtaleVaryingSystemPullback

/-! # Inverse image of varying-torsor coefficient systems along arbitrary morphisms -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtaleDirectImage Langlands.Geometry.EtaleInverseImage

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]


section Constant

variable {G : Type u} [Group G] (Y : Action X.Etale G)

/-- For constant module coefficients, the comparison followed by the constant-sheaf comparison
gives a map from the inverse image of the associated sheaf to the associated sheaf on `Z`. -/
def inverseImageConstantAssociatedMap :
    etaleAssociatedFunctor (R := R) X Y ⋙ inverseImage f R ⟶
      etaleAssociatedFunctor Z ((etaleTorsorPullbackFunctor f G).obj Y) :=
  Functor.whiskerLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G)
      (inverseImageAssociatedMap f R Y) ≫
    Functor.whiskerRight (inverseImageConstantActionIso f R G).hom
      (associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y))

/-- The constant-coefficient comparison on invariant sections: inverse image of the original
inclusion, the base-change map, and the constant-sheaf comparison on the cover. -/
@[reassoc] theorem inverseImageConstantAssociatedMap_inclusion (M : Action (ModuleCat.{u} R) G) :
    (inverseImageConstantAssociatedMap f R Y).app M ≫
        inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) =
      (inverseImage f R).map (inclusion X.smallEtaleTopology Y
          (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)) ≫
        inverseImageProductSheafMap f R Y.V
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V) ≫
          (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj Y.V)).map
            ((inverseImageConstantIso f R).hom.app M.V) := by
  change ((inverseImageAssociatedMap f R Y).app _ ≫
      (associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)).map
        ((inverseImageConstantActionIso f R G).hom.app M)) ≫ _ = _
  rw [Category.assoc, inclusion_natural, inverseImageAssociatedMap_inclusion_assoc,
    inverseImageConstantActionIso_hom_hom]
  rfl

/-- For a finite geometric torsor, inverse image along an arbitrary morphism of the associated
sheaf of a module representation is the associated sheaf of the base-changed torsor and the same
representation. -/
def inverseImageConstantAssociatedIso (hY : IsFiniteGeometricTorsor X Y) :
    etaleAssociatedFunctor (R := R) X Y ⋙ inverseImage f R ≅
      etaleAssociatedFunctor Z ((etaleTorsorPullbackFunctor f G).obj Y) :=
  Functor.isoWhiskerLeft ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G)
      (inverseImageAssociatedIso f R Y hY) ≪≫
    Functor.isoWhiskerRight (inverseImageConstantActionIso f R G)
      (associatedFunctor Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y))

@[simp] theorem inverseImageConstantAssociatedIso_hom (hY : IsFiniteGeometricTorsor X Y) :
    (inverseImageConstantAssociatedIso f R Y hY).hom = inverseImageConstantAssociatedMap f R Y :=
  rfl

/-- The forward comparison on invariant sections. -/
@[reassoc] theorem inverseImageConstantAssociatedIso_hom_inclusion
    (hY : IsFiniteGeometricTorsor X Y) (M : Action (ModuleCat.{u} R) G) :
    (inverseImageConstantAssociatedIso f R Y hY).hom.app M ≫
        inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) =
      (inverseImage f R).map (inclusion X.smallEtaleTopology Y
          (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)) ≫
        (inverseImageProductSheafIso f R Y hY
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V)).hom ≫
          (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj Y.V)).map
            ((inverseImageConstantIso f R).hom.app M.V) :=
  inverseImageConstantAssociatedMap_inclusion f R Y M

/-- The inverse comparison on invariant sections. -/
@[reassoc] theorem inverseImageConstantAssociatedIso_inv_inclusion
    (hY : IsFiniteGeometricTorsor X Y) (M : Action (ModuleCat.{u} R) G) :
    (inverseImageConstantAssociatedIso f R Y hY).inv.app M ≫
        (inverseImage f R).map (inclusion X.smallEtaleTopology Y
          (((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M)) =
      inclusion Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f G).obj Y)
          (((constantSheaf Z.smallEtaleTopology (ModuleCat.{u} R)).mapAction G).obj M) ≫
        (productSheaf Z.smallEtaleTopology ((etaleObjectPullback f).obj Y.V)).map
            ((inverseImageConstantIso f R).inv.app M.V) ≫
          (inverseImageProductSheafIso f R Y hY
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V)).inv := by
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, inverseImageConstantAssociatedIso_hom,
    inverseImageConstantAssociatedMap_inclusion_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hP := (inverseImageProductSheafIso f R Y hY
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V)).hom_inv_id
  rw [inverseImageProductSheafIso_hom] at hP
  rw [hP]
  exact (Category.comp_id _).symm

variable {H : Type u} [Group H] {Y' : Action X.Etale H}
variable (φ : H →* G) (a : Y' ⟶ (Action.res X.Etale φ).obj Y)

/-- The constant-coefficient comparison respects every compatible cover and coefficient map,
including changes of deck group. -/
@[reassoc] theorem inverseImageConstantAssociatedMap_crossCover
    {M : Action (ModuleCat.{u} R) G} {N : Action (ModuleCat.{u} R) H}
    (c : (Action.res (ModuleCat.{u} R) φ).obj M ⟶ N) :
    (inverseImage f R).map (etaleCrossCoverMap X φ a c) ≫
        (inverseImageConstantAssociatedMap f R Y').app N =
      (inverseImageConstantAssociatedMap f R Y).app M ≫
        etaleCrossCoverMap Z φ ((etaleTorsorPullbackFunctor f H).map a) c := by
  dsimp only [etaleCrossCoverMap, constantCrossCoverMap]
  apply hom_ext Z.smallEtaleTopology ((etaleTorsorPullbackFunctor f H).obj Y')
  rw [Category.assoc, inverseImageConstantAssociatedMap_inclusion,
    ← CategoryTheory.Functor.map_comp_assoc]
  erw [crossCoverMap_inclusion]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [inverseImageProductSheafMap_natural_assoc f R Y'.V
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map c.hom)]
  erw [inverseImageProductSheafMap_coverPullback_assoc f R a.hom
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} R)).obj M.V)]
  rw [crossCoverMap_inclusion]
  erw [inverseImageConstantAssociatedMap_inclusion_assoc f R Y M]
  simp only [etaleTorsorPullbackFunctor, Functor.mapAction_map_hom,
    Functor.mapAction_obj_V, Action.res_obj_V]
  rw [← coverPullback_natural_assoc Z.smallEtaleTopology
    (Y := (etaleObjectPullback f).obj Y.V)
    (Z := (etaleObjectPullback f).obj Y'.V)
    ((etaleObjectPullback f).map a.hom)
    ((inverseImageConstantIso f R).hom.app M.V)]
  simp only [← CategoryTheory.Functor.map_comp]
  erw [(inverseImageConstantIso f R).hom.naturality c.hom]
  rfl

end Constant

section Varying

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)
variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))

/-- Inverse image of one vertex, natural in the entire coefficient diagram. -/
def inverseImageAssociatedAtIso (i : I) :
    etaleAssociatedAt (R := R) X Y i ⋙ inverseImage f R ≅
      etaleAssociatedAt Z ((etaleTorsorDiagramPullback f D).obj Y) i :=
  Functor.isoWhiskerLeft (EquivariantDiagram.evaluation i)
    (inverseImageConstantAssociatedIso f R (Y.action i) (hY i))

/-- Inverse image of the common target of coefficient reduction and cover change. -/
def inverseImageAssociatedTransitionTargetIso {i j : I} (b : i ⟶ j) :
    etaleAssociatedTransitionTarget (R := R) X Y b ⋙ inverseImage f R ≅
      etaleAssociatedTransitionTarget Z ((etaleTorsorDiagramPullback f D).obj Y) b :=
  Functor.isoWhiskerLeft
    (EquivariantDiagram.evaluation j ⋙ Action.res (ModuleCat.{u} R) (D.map b).hom)
    (inverseImageConstantAssociatedIso f R (Y.action i) (hY i))

/-- The coefficient-reduction leg commutes with the comparisons. -/
@[reassoc] theorem etaleAssociatedReduction_inverseImage {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (inverseImage f R).map ((etaleAssociatedReduction X Y b).app M) ≫
        (inverseImageAssociatedTransitionTargetIso f R Y hY b).hom.app M =
      (inverseImageAssociatedAtIso f R Y hY i).hom.app M ≫
        (etaleAssociatedReduction Z ((etaleTorsorDiagramPullback f D).obj Y) b).app M :=
  (inverseImageConstantAssociatedIso f R (Y.action i) (hY i)).hom.naturality (M.transition b)

/-- The cover-change leg commutes with inverse image and geometric base change of covers. -/
@[reassoc] theorem etaleAssociatedComparison_inverseImage {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (inverseImage f R).map ((etaleAssociatedComparison X Y b).app M) ≫
        (inverseImageAssociatedTransitionTargetIso f R Y hY b).hom.app M =
      (inverseImageAssociatedAtIso f R Y hY j).hom.app M ≫
        (etaleAssociatedComparison Z ((etaleTorsorDiagramPullback f D).obj Y) b).app M :=
  inverseImageConstantAssociatedMap_crossCover f R (Y.action j) (D.map b).hom (Y.transition b)
    (𝟙 ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j)))

/-- The actual inverse-cover transition commutes with inverse image along `f`. -/
@[reassoc] theorem etaleAssociatedTransition_inverseImage {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (inverseImage f R).map ((etaleAssociatedTransition X Y hY b).app M) ≫
        (inverseImageAssociatedAtIso f R Y hY j).hom.app M =
      (inverseImageAssociatedAtIso f R Y hY i).hom.app M ≫
        (etaleAssociatedTransition Z ((etaleTorsorDiagramPullback f D).obj Y)
          (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY) b).app M := by
  let := etaleAssociatedComparison_app_isIso Z
    ((etaleTorsorDiagramPullback f D).obj Y)
    (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY) b M
  apply (cancel_mono
    ((etaleAssociatedComparison Z ((etaleTorsorDiagramPullback f D).obj Y) b).app M)).1
  rw [Category.assoc, ← etaleAssociatedComparison_inverseImage,
    ← Category.assoc, ← Functor.map_comp,
    etaleAssociatedTransition_comparison, etaleAssociatedReduction_inverseImage,
    Category.assoc, etaleAssociatedTransition_comparison]

/-- Inverse image along an arbitrary morphism of the entire associated coefficient-system functor
is naturally isomorphic to the functor on the base-changed finite torsors, with the same group
diagram and the same coefficient diagrams. -/
def etaleAssociatedVaryingSystemInverseImage :
    etaleAssociatedVaryingSystemFunctor (R := R) X Y hY ⋙
        (Functor.whiskeringRight I _ _).obj (inverseImage f R) ≅
      etaleAssociatedVaryingSystemFunctor Z ((etaleTorsorDiagramPullback f D).obj Y)
        (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY) :=
  NatIso.ofComponents
    (fun M => NatIso.ofComponents
      (fun i => (inverseImageAssociatedAtIso f R Y hY i).app M)
      (fun b => etaleAssociatedTransition_inverseImage f R Y hY b M))
    (by
      intro M N c
      apply NatTrans.ext
      funext i
      exact (inverseImageAssociatedAtIso f R Y hY i).hom.naturality c)

/-- The forward system comparison uses the associated-sheaf comparison at every index. -/
@[simp] theorem etaleAssociatedVaryingSystemInverseImage_hom_app
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    ((etaleAssociatedVaryingSystemInverseImage f R Y hY).hom.app M).app i =
      (inverseImageConstantAssociatedIso f R (Y.action i) (hY i)).hom.app (M.action i) := rfl

/-- The inverse system comparison uses the inverse component. -/
@[simp] theorem etaleAssociatedVaryingSystemInverseImage_inv_app
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    ((etaleAssociatedVaryingSystemInverseImage f R Y hY).inv.app M).app i =
      (inverseImageConstantAssociatedIso f R (Y.action i) (hY i)).inv.app (M.action i) := rfl

/-- The inverse comparison also intertwines the complete inverse-cover transition. -/
@[reassoc] theorem etaleAssociatedTransition_inverseImage_inv {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (etaleAssociatedTransition Z ((etaleTorsorDiagramPullback f D).obj Y)
        (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY) b).app M ≫
        (inverseImageAssociatedAtIso f R Y hY j).inv.app M =
      (inverseImageAssociatedAtIso f R Y hY i).inv.app M ≫
        (inverseImage f R).map ((etaleAssociatedTransition X Y hY b).app M) :=
  ((etaleAssociatedVaryingSystemInverseImage f R Y hY).inv.app M).naturality b

end Varying

end Langlands.Shimura.Coefficients

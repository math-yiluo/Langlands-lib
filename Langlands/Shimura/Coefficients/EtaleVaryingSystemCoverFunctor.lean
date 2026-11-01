import Langlands.Shimura.Coefficients.EtaleVaryingSystemPullback
import Langlands.Shimura.Coefficients.VaryingSystemCoverChange
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Cover functoriality of finite-torsor systems and their etale base change -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {I : Type uI} [Category.{vI} I]

/-- The full category of actual cover diagrams whose vertices are finite
geometric torsors, retaining all equivariant diagram morphisms. -/
abbrev FiniteGeometricTorsorDiagram (X : Scheme.{u}) (D : I ⥤ GrpCat.{u}) :=
  ObjectProperty.FullSubcategory
    (fun Y : EquivariantDiagram D X.Etale =>
      ∀ i, IsFiniteGeometricTorsor X (Y.action i))

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (D : I ⥤ GrpCat.{u})

/-- Geometric base change lifts to finite-torsor diagrams for every base map. -/
def etaleFiniteTorsorDiagramPullback :
    FiniteGeometricTorsorDiagram X D ⥤ FiniteGeometricTorsorDiagram Z D where
  obj Y :=
    ⟨(etaleTorsorDiagramPullback f D).obj Y.obj,
      etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y.obj Y.property⟩
  map a := ObjectProperty.homMk ((etaleTorsorDiagramPullback f D).map a.hom)
  map_id Y := by
    apply ObjectProperty.hom_ext
    exact (etaleTorsorDiagramPullback f D).map_id Y.obj
  map_comp a b := by
    apply ObjectProperty.hom_ext
    exact (etaleTorsorDiagramPullback f D).map_comp a.hom b.hom

@[simp] theorem etaleFiniteTorsorDiagramPullback_obj
    (Y : FiniteGeometricTorsorDiagram X D) :
    ((etaleFiniteTorsorDiagramPullback f D).obj Y).obj =
      (etaleTorsorDiagramPullback f D).obj Y.obj := rfl

@[simp] theorem etaleFiniteTorsorDiagramPullback_map
    {Y T : FiniteGeometricTorsorDiagram X D} (a : Y ⟶ T) :
    ((etaleFiniteTorsorDiagramPullback f D).map a).hom =
      (etaleTorsorDiagramPullback f D).map a.hom := rfl

variable (X) (R : Type u) [CommRing R]

/-- The associated whole-system functor is contravariant in the finite-torsor
cover diagram and covariant in the equivariant coefficient diagram. -/
def etaleAssociatedVaryingSystemCoverFunctor :
    (FiniteGeometricTorsorDiagram X D)ᵒᵖ ⥤
      (EquivariantDiagram D (ModuleCat.{u} R) ⥤
        (I ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R))) where
  obj Y := etaleAssociatedVaryingSystemFunctor X Y.unop.obj Y.unop.property
  map a := etaleAssociatedVaryingSystemCoverChange X R
    _ _ a.unop.hom
  map_id Y := etaleAssociatedVaryingSystemCoverChange_id X R Y.unop.property
  map_comp a b := by
    exact (etaleAssociatedVaryingSystemCoverChange_comp X R
      _ _ _ b.unop.hom a.unop.hom).symm

@[simp] theorem etaleAssociatedVaryingSystemCoverFunctor_obj
    (Y : FiniteGeometricTorsorDiagram X D) :
    (etaleAssociatedVaryingSystemCoverFunctor X D R).obj (op Y) =
      etaleAssociatedVaryingSystemFunctor X Y.obj Y.property := rfl

/-- Cover functor components are the actual invariant-section cross-cover maps. -/
@[simp] theorem etaleAssociatedVaryingSystemCoverFunctor_map_app_app
    {Y T : FiniteGeometricTorsorDiagram X D} (a : Y ⟶ T)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    (((etaleAssociatedVaryingSystemCoverFunctor X D R).map a.op).app M).app i =
      etaleCrossCoverMap X (MonoidHom.id (D.obj i))
        ((EquivariantDiagram.evaluation i).map a.hom) (𝟙 (M.action i)) := rfl

variable {X D} [Etale f]
variable {Y T : EquivariantDiagram D X.Etale}
variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
variable (hT : ∀ i, IsFiniteGeometricTorsor X (T.action i))

/-- The full system base-change comparison commutes with every cover-diagram
map over the fixed base and varying-group diagram. -/
@[reassoc] theorem etaleAssociatedVaryingSystemCoverChange_pullback (a : Y ⟶ T) :
    Functor.whiskerRight (etaleAssociatedVaryingSystemCoverChange X R hY hT a)
        ((Functor.whiskeringRight I _ _).obj
          (EtalePullback.restriction f (ModuleCat.{u} R))) ≫
        (etaleAssociatedVaryingSystemPullback f R Y hY).hom =
      (etaleAssociatedVaryingSystemPullback f R T hT).hom ≫
        etaleAssociatedVaryingSystemCoverChange Z R
          (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY)
          (etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D T hT)
          ((etaleTorsorDiagramPullback f D).map a) := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext i
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskeringRight_obj_map, etaleAssociatedVaryingSystemCoverChange_app,
    etaleAssociatedVaryingSystemPullback_hom_app]
  exact etaleConstantAssociatedPullback_crossCover f R
    (Y := T.action i) (Y' := Y.action i) (MonoidHom.id (D.obj i))
    ((EquivariantDiagram.evaluation i).map a)
    (M := M.action i) (N := M.action i) (𝟙 (M.action i))

variable (D)

/-- Etale restriction of associated whole systems is naturally isomorphic to
geometric pullback of their covers, naturally in the entire cover category. -/
def etaleAssociatedVaryingSystemPullbackCoverNatural :
    etaleAssociatedVaryingSystemCoverFunctor X D R ⋙
        (Functor.whiskeringRight (EquivariantDiagram D (ModuleCat.{u} R)) _ _).obj
          ((Functor.whiskeringRight I _ _).obj
            (EtalePullback.restriction f (ModuleCat.{u} R))) ≅
      (etaleFiniteTorsorDiagramPullback f D).op ⋙
        etaleAssociatedVaryingSystemCoverFunctor Z D R :=
  NatIso.ofComponents
    (fun Y => etaleAssociatedVaryingSystemPullback f R Y.unop.obj Y.unop.property)
    (fun a => etaleAssociatedVaryingSystemCoverChange_pullback f R
      _ _ a.unop.hom)

@[simp] theorem etaleAssociatedVaryingSystemPullbackCoverNatural_hom_app_app_app
    (Y : FiniteGeometricTorsorDiagram X D)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) (i : I) :
    ((((etaleAssociatedVaryingSystemPullbackCoverNatural f D R).hom.app
        (op Y)).app M).app i) =
      (etaleConstantAssociatedPullback f R (Y.obj.action i)).hom.app
        (M.action i) := rfl

end Langlands.Shimura.Coefficients

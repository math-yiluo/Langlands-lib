import Langlands.Shimura.Coefficients.EtaleInverseImageVaryingSystem
import Langlands.Shimura.Coefficients.VaryingSystemGroupCoverChange
import Mathlib.CategoryTheory.Comma.Arrow

/-! # Inverse image and varying-group cover comparison -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry.EtaleInverseImage

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) (R : Type u) [CommRing R]
  {I : Type uI} [Category.{vI} I] {D E : I ⥤ GrpCat.{u}}
  (φ : D ⟶ E) (Y : EquivariantDiagram D X.Etale)
  (V : EquivariantDiagram E X.Etale)
  (a : Y ⟶ (EquivariantDiagram.groupRestriction X.Etale φ).obj V)

local notation "pulledY" => (etaleTorsorDiagramPullback f D).obj Y
local notation "pulledV" => (etaleTorsorDiagramPullback f E).obj V
local notation "restriction" => EquivariantDiagram.groupRestriction (ModuleCat R) φ

/-- Pullback of the original diagram map, with the same natural map of deck groups. -/
def etaleGroupCoverMapPullback :
    pulledY ⟶ (EquivariantDiagram.groupRestriction Z.Etale φ).obj pulledV :=
  (etaleTorsorDiagramPullback f D).map a

/-- Every component is the actual pullback of the original equivariant cover map. -/
@[simp] theorem etaleGroupCoverMapPullback_evaluation (i : I) :
    (EquivariantDiagram.evaluation i).map (etaleGroupCoverMapPullback f φ Y V a) =
      (etaleTorsorPullbackFunctor f (D.obj i)).map
        ((EquivariantDiagram.evaluation i).map a) := rfl

variable (hY : ∀ i, IsFiniteGeometricTorsor X (Y.action i))
  (hV : ∀ i, IsFiniteGeometricTorsor X (V.action i))

local notation "pulledhY" =>
  etaleTorsorDiagramPullback_isFiniteGeometricTorsor f D Y hY
local notation "pulledhV" =>
  etaleTorsorDiagramPullback_isFiniteGeometricTorsor f E V hV
local notation "pullSystems" =>
  (Functor.whiskeringRight I _ _).obj (inverseImage f R)
local notation "originalCoverIso" =>
  etaleAssociatedVaryingGroupCoverIso X R φ Y V a hY hV
local notation "pulledCoverIso" =>
  etaleAssociatedVaryingGroupCoverIso Z R φ pulledY pulledV
    (etaleGroupCoverMapPullback f φ Y V a) pulledhY pulledhV
local notation "inverseY" => etaleAssociatedVaryingSystemInverseImage f R Y hY
local notation "inverseV" => etaleAssociatedVaryingSystemInverseImage f R V hV

/-- The full group-and-cover comparison commutes with genuine inverse image. -/
@[reassoc] theorem etaleAssociatedVaryingGroupCoverIso_inverseImage_hom
    (M : EquivariantDiagram E (ModuleCat.{u} R)) :
    (pullSystems).map ((originalCoverIso).hom.app M) ≫
        (inverseY).hom.app ((restriction).obj M) =
      (inverseV).hom.app M ≫ (pulledCoverIso).hom.app M := by
  apply NatTrans.ext
  funext i
  exact inverseImageConstantAssociatedMap_crossCover f R (V.action i) (φ.app i).hom
    ((EquivariantDiagram.evaluation i).map a)
    (𝟙 ((Action.res (ModuleCat.{u} R) (φ.app i).hom).obj (M.action i)))

/-- Inverting the cover comparison preserves the same whole-system square. -/
@[reassoc] theorem etaleAssociatedVaryingGroupCoverIso_inverseImage_inv
    (M : EquivariantDiagram E (ModuleCat.{u} R)) :
    (pullSystems).map ((originalCoverIso).inv.app M) ≫ (inverseV).hom.app M =
      (inverseY).hom.app ((restriction).obj M) ≫ (pulledCoverIso).inv.app M := by
  apply (cancel_mono ((pulledCoverIso).hom.app M)).1
  rw [Category.assoc,
    ← etaleAssociatedVaryingGroupCoverIso_inverseImage_hom f R φ Y V a hY hV M,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

/-- The entire inverse-image cover-comparison arrow is identified with the comparison
of the actual base-changed covers by the two constructed inverse-image isomorphisms. -/
def etaleAssociatedVaryingGroupCoverInverseImageArrowIso
    (M : EquivariantDiagram E (ModuleCat.{u} R)) :
    Arrow.mk ((pullSystems).map ((originalCoverIso).hom.app M)) ≅
      Arrow.mk ((pulledCoverIso).hom.app M) :=
  Arrow.isoMk ((inverseV).app M) ((inverseY).app ((restriction).obj M))
    (etaleAssociatedVaryingGroupCoverIso_inverseImage_hom f R φ Y V a hY hV M).symm

end Langlands.Shimura.Coefficients

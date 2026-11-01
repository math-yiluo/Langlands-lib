import Langlands.Shimura.Coefficients.VaryingCover
import Langlands.Shimura.Coefficients.EtaleCrossCoverPullback

/-! # Etale base change of varying-cover coefficient cospans -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [Etale f]
variable (R : Type u) [CommRing R]
variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)

/-- Base change of one vertex, natural in the entire coefficient diagram. -/
def etaleAssociatedAtPullback (i : I) :
    etaleAssociatedAt (R := R) X Y i ⋙
        EtalePullback.restriction f (ModuleCat.{u} R) ≅
      etaleAssociatedAt Z ((etaleTorsorDiagramPullback f D).obj Y) i :=
  Functor.isoWhiskerLeft (EquivariantDiagram.evaluation i)
    (etaleConstantAssociatedPullback f R (Y.action i))

/-- Base change of the common target of coefficient reduction and cover change. -/
def etaleAssociatedTransitionTargetPullback {i j : I} (b : i ⟶ j) :
    etaleAssociatedTransitionTarget (R := R) X Y b ⋙
        EtalePullback.restriction f (ModuleCat.{u} R) ≅
      etaleAssociatedTransitionTarget Z ((etaleTorsorDiagramPullback f D).obj Y) b :=
  Functor.isoWhiskerLeft
    (EquivariantDiagram.evaluation j ⋙ Action.res (ModuleCat.{u} R) (D.map b).hom)
    (etaleConstantAssociatedPullback f R (Y.action i))

/-- The coefficient-reduction leg commutes with the constructed comparisons. -/
@[reassoc] theorem etaleAssociatedReduction_pullback {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (EtalePullback.restriction f (ModuleCat.{u} R)).map
        ((etaleAssociatedReduction X Y b).app M) ≫
        (etaleAssociatedTransitionTargetPullback f R Y b).hom.app M =
      (etaleAssociatedAtPullback f R Y i).hom.app M ≫
        (etaleAssociatedReduction Z ((etaleTorsorDiagramPullback f D).obj Y) b).app M :=
  (etaleConstantAssociatedPullback f R (Y.action i)).hom.naturality (M.transition b)

/-- The cover-change leg commutes with restriction and actual geometric base change. -/
@[reassoc] theorem etaleAssociatedComparison_pullback {i j : I} (b : i ⟶ j)
    (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    (EtalePullback.restriction f (ModuleCat.{u} R)).map
        ((etaleAssociatedComparison X Y b).app M) ≫
        (etaleAssociatedTransitionTargetPullback f R Y b).hom.app M =
      (etaleAssociatedAtPullback f R Y j).hom.app M ≫
        (etaleAssociatedComparison Z ((etaleTorsorDiagramPullback f D).obj Y) b).app M :=
  etaleConstantAssociatedPullback_crossCover f R (D.map b).hom (Y.transition b)
    (𝟙 ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j)))

/-- The complete transition cospan commutes with etale base change, naturally in
every coefficient diagram and every morphism of such diagrams. -/
def etaleAssociatedTransitionCospanPullback {i j : I} (b : i ⟶ j) :
    etaleAssociatedTransitionCospan (R := R) X Y b ⋙
        (Functor.whiskeringRight WalkingCospan _ _).obj
          (EtalePullback.restriction f (ModuleCat.{u} R)) ≅
      etaleAssociatedTransitionCospan Z ((etaleTorsorDiagramPullback f D).obj Y) b :=
  NatIso.ofComponents
    (fun M => cospanIsoMk
      ((etaleAssociatedTransitionTargetPullback f R Y b).app M)
      ((etaleAssociatedAtPullback f R Y i).app M)
      ((etaleAssociatedAtPullback f R Y j).app M)
      (etaleAssociatedReduction_pullback f R Y b M)
      (etaleAssociatedComparison_pullback f R Y b M))
    (by
      intro M N c
      apply NatTrans.ext
      funext w
      rcases w with (_ | _ | _)
      · exact (etaleAssociatedTransitionTargetPullback f R Y b).hom.naturality c
      · exact (etaleAssociatedAtPullback f R Y i).hom.naturality c
      · exact (etaleAssociatedAtPullback f R Y j).hom.naturality c)

@[simp] theorem etaleAssociatedTransitionCospanPullback_hom_app_left
    {i j : I} (b : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    ((etaleAssociatedTransitionCospanPullback f R Y b).hom.app M).app WalkingCospan.left =
      (etaleConstantAssociatedPullback f R (Y.action i)).hom.app (M.action i) := rfl

@[simp] theorem etaleAssociatedTransitionCospanPullback_hom_app_right
    {i j : I} (b : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    ((etaleAssociatedTransitionCospanPullback f R Y b).hom.app M).app WalkingCospan.right =
      (etaleConstantAssociatedPullback f R (Y.action j)).hom.app (M.action j) := rfl

@[simp] theorem etaleAssociatedTransitionCospanPullback_hom_app_one
    {i j : I} (b : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    ((etaleAssociatedTransitionCospanPullback f R Y b).hom.app M).app WalkingCospan.one =
      (etaleConstantAssociatedPullback f R (Y.action i)).hom.app
        ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j)) := rfl

@[simp] theorem etaleAssociatedTransitionCospanPullback_inv_app_left
    {i j : I} (b : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    ((etaleAssociatedTransitionCospanPullback f R Y b).inv.app M).app WalkingCospan.left =
      (etaleConstantAssociatedPullback f R (Y.action i)).inv.app (M.action i) := rfl

@[simp] theorem etaleAssociatedTransitionCospanPullback_inv_app_right
    {i j : I} (b : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    ((etaleAssociatedTransitionCospanPullback f R Y b).inv.app M).app WalkingCospan.right =
      (etaleConstantAssociatedPullback f R (Y.action j)).inv.app (M.action j) := rfl

@[simp] theorem etaleAssociatedTransitionCospanPullback_inv_app_one
    {i j : I} (b : i ⟶ j) (M : EquivariantDiagram D (ModuleCat.{u} R)) :
    ((etaleAssociatedTransitionCospanPullback f R Y b).inv.app M).app WalkingCospan.one =
      (etaleConstantAssociatedPullback f R (Y.action i)).inv.app
        ((Action.res (ModuleCat.{u} R) (D.map b).hom).obj (M.action j)) := rfl

end Langlands.Shimura.Coefficients

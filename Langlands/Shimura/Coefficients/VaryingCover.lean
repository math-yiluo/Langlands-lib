import Langlands.CategoryTheory.EquivariantDiagram
import Langlands.Shimura.Coefficients.EtaleCrossCover
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-! # Associated coefficient cospans for varying covers and groups -/

noncomputable section

universe u uI vI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {G H : Type u} [Group G] [Group H]
variable {Y : Action X.Etale G} {Z : Action X.Etale H}

/-- The canonical cover-comparison map, natural in the coefficient representation. -/
def etaleAssociatedCoverChange (φ : H →* G)
    (a : Z ⟶ (Action.res X.Etale φ).obj Y) :
    etaleAssociatedFunctor (R := R) X Y ⟶
      Action.res (ModuleCat.{u} R) φ ⋙ etaleAssociatedFunctor X Z where
  app M := etaleCrossCoverMap X φ a (𝟙 ((Action.res _ φ).obj M))
  naturality {M N} c := by
    simp only [etaleCrossCoverMap, constantCrossCoverMap, CategoryTheory.Functor.map_id]
    exact (associatedCoverChange (Scheme.smallEtaleTopology X) φ a).naturality
      (((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)).mapAction G).map c)

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)

/-- Associate sheaves at one index, functorially in the whole coefficient diagram. -/
def etaleAssociatedAt (i : I) :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R) :=
  EquivariantDiagram.evaluation i ⋙ etaleAssociatedFunctor X (Y.action i)

/-- The common target for coefficient reduction and contravariant cover comparison. -/
def etaleAssociatedTransitionTarget {i j : I} (f : i ⟶ j) :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R) :=
  EquivariantDiagram.evaluation j ⋙ Action.res (ModuleCat.{u} R) (D.map f).hom ⋙
    etaleAssociatedFunctor X (Y.action i)

/-- Reduction of coefficients on the source cover, natural in coefficient diagrams. -/
def etaleAssociatedReduction {i j : I} (f : i ⟶ j) :
    etaleAssociatedAt (R := R) X Y i ⟶
      etaleAssociatedTransitionTarget (R := R) X Y f where
  app M := (etaleAssociatedFunctor X (Y.action i)).map (M.transition f)
  naturality {M N} c := by
    change (etaleAssociatedFunctor X (Y.action i)).map
        ((EquivariantDiagram.evaluation i).map c) ≫
        (etaleAssociatedFunctor X (Y.action i)).map (N.transition f) =
      (etaleAssociatedFunctor X (Y.action i)).map (M.transition f) ≫
        (etaleAssociatedFunctor X (Y.action i)).map
          ((Action.res (ModuleCat.{u} R) (D.map f).hom).map
            ((EquivariantDiagram.evaluation j).map c))
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply Action.Hom.ext
    exact (c.hom.naturality f).symm

/-- Contravariant cover comparison, natural in coefficient diagrams. -/
def etaleAssociatedComparison {i j : I} (f : i ⟶ j) :
    etaleAssociatedAt (R := R) X Y j ⟶
      etaleAssociatedTransitionTarget (R := R) X Y f :=
  Functor.whiskerLeft (EquivariantDiagram.evaluation j)
    (etaleAssociatedCoverChange X (D.map f).hom (Y.transition f))

/-- Each index arrow gives an actual cospan of associated sheaves, functorial in
the coefficient diagram. Its right leg has not been inverted. -/
def etaleAssociatedTransitionCospan {i j : I} (f : i ⟶ j) :
    EquivariantDiagram D (ModuleCat.{u} R) ⥤
      (WalkingCospan ⥤ Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u} R)) :=
  (cospan (etaleAssociatedReduction X Y f) (etaleAssociatedComparison X Y f)).flip

variable (M : EquivariantDiagram D (ModuleCat.{u} R))

@[simp] theorem etaleAssociatedTransitionCospan_left {i j : I} (f : i ⟶ j) :
    ((etaleAssociatedTransitionCospan X Y f).obj M).obj WalkingCospan.left =
      (etaleAssociatedFunctor X (Y.action i)).obj (M.action i) := rfl

@[simp] theorem etaleAssociatedTransitionCospan_right {i j : I} (f : i ⟶ j) :
    ((etaleAssociatedTransitionCospan X Y f).obj M).obj WalkingCospan.right =
      (etaleAssociatedFunctor X (Y.action j)).obj (M.action j) := rfl

@[simp] theorem etaleAssociatedTransitionCospan_one {i j : I} (f : i ⟶ j) :
    ((etaleAssociatedTransitionCospan X Y f).obj M).obj WalkingCospan.one =
      (etaleAssociatedFunctor X (Y.action i)).obj
        ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j)) := rfl

@[simp] theorem etaleAssociatedTransitionCospan_inl {i j : I} (f : i ⟶ j) :
    ((etaleAssociatedTransitionCospan X Y f).obj M).map WalkingCospan.Hom.inl =
      (etaleAssociatedFunctor X (Y.action i)).map (M.transition f) := rfl

@[simp] theorem etaleAssociatedTransitionCospan_inr {i j : I} (f : i ⟶ j) :
    ((etaleAssociatedTransitionCospan X Y f).obj M).map WalkingCospan.Hom.inr =
      etaleCrossCoverMap X (D.map f).hom (Y.transition f)
        (𝟙 ((Action.res (ModuleCat.{u} R) (D.map f).hom).obj (M.action j))) := rfl

end Langlands.Shimura.Coefficients

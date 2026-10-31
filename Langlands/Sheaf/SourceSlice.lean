import Langlands.Sheaf.SliceMap

/-! # Source changes for diagrams restricted to slice sites -/

noncomputable section

universe uC vC uA vA uI vI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Sheaf

open CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable (J : GrothendieckTopology C) (A : Type uA) [Category.{vA} A]
variable {I : Type uI} [Category.{vI} I] (Y : I ⥤ C)

/-- The part of a global sheaf diagram reachable from `k`, on the slice at `Y k`. -/
def sourceSliceDiagram (k : I) (F : I ⥤ Sheaf J A) :
    Under k ⥤ Sheaf (J.over (Y.obj k)) A :=
  Under.forget k ⋙ F ⋙ J.overPullback A (Y.obj k)

/-- Restrict a whole diagram from the target slice to the source slice. -/
def sourceSliceRestriction {k l : I} (f : k ⟶ l) :
    (Under l ⥤ Sheaf (J.over (Y.obj l)) A) ⥤
      (Under l ⥤ Sheaf (J.over (Y.obj k)) A) :=
  (Functor.whiskeringRight _ _ _).obj (J.overMapPullback A (Y.map f))

/-- Reindex a source-slice diagram by precomposition of its outgoing arrows. -/
def sourceSliceReindex {k l : I} (f : k ⟶ l) :
    (Under k ⥤ Sheaf (J.over (Y.obj k)) A) ⥤
      (Under l ⥤ Sheaf (J.over (Y.obj k)) A) :=
  (Functor.whiskeringLeft _ _ _).obj (Under.map f)

/-- Changing a source cover agrees with reindexing the reachable global terms. -/
def sourceSliceChangeIso {k l : I} (f : k ⟶ l) (F : I ⥤ Sheaf J A) :
    (sourceSliceRestriction J A Y f).obj (sourceSliceDiagram J A Y l F) ≅
      (sourceSliceReindex J A Y f).obj (sourceSliceDiagram J A Y k F) :=
  NatIso.ofComponents
    (fun i => (overPullbackMapIso J A (Y.map f)).app (F.obj i.right))
    (fun c => (overPullbackMapIso J A (Y.map f)).hom.naturality (F.map c.right))

@[simp] theorem sourceSliceChangeIso_hom_app_hom_app
    {k l : I} (f : k ⟶ l) (F : I ⥤ Sheaf J A)
    (i : Under l) (U : (Over (Y.obj k))ᵒᵖ) :
    ((sourceSliceChangeIso J A Y f F).hom.app i).hom.app U = 𝟙 _ := rfl

@[simp] theorem sourceSliceChangeIso_inv_app_hom_app
    {k l : I} (f : k ⟶ l) (F : I ⥤ Sheaf J A)
    (i : Under l) (U : (Over (Y.obj k))ᵒᵖ) :
    ((sourceSliceChangeIso J A Y f F).inv.app i).hom.app U = 𝟙 _ := rfl

/-- Source-local diagrams are functorial in the original global diagram. -/
def sourceSliceDiagramFunctor (k : I) :
    (I ⥤ Sheaf J A) ⥤ (Under k ⥤ Sheaf (J.over (Y.obj k)) A) :=
  (Functor.whiskeringLeft _ _ _).obj (Under.forget k) ⋙
    (Functor.whiskeringRight _ _ _).obj (J.overPullback A (Y.obj k))

/-- The change comparison is natural in all global sheaf-diagram morphisms. -/
def sourceSliceChangeFunctorIso {k l : I} (f : k ⟶ l) :
    sourceSliceDiagramFunctor J A Y l ⋙ sourceSliceRestriction J A Y f ≅
      sourceSliceDiagramFunctor J A Y k ⋙ sourceSliceReindex J A Y f :=
  NatIso.ofComponents (sourceSliceChangeIso J A Y f)
    (fun c => by
      ext i U
      simp [sourceSliceRestriction, sourceSliceReindex, sourceSliceDiagramFunctor,
        sourceSliceDiagram])

/-- The identity source change is the standard slice identity comparison,
after applying the cover diagram's identity law. -/
theorem sourceSliceChangeIso_id (k : I) (F : I ⥤ Sheaf J A) (i : Under k) :
    (sourceSliceChangeIso J A Y (𝟙 k) F).hom.app i =
      (J.overMapPullbackCongr A (Y.map_id k)).hom.app
          ((sourceSliceDiagram J A Y k F).obj i) ≫
        (J.overMapPullbackId A (Y.obj k)).hom.app
          ((sourceSliceDiagram J A Y k F).obj i) := by
  ext U
  simp [sourceSliceDiagram, sourceSliceRestriction]

/-- Successive source changes equal direct change, with the standard slice
composition comparison and the cover diagram's composition law. -/
theorem sourceSliceChangeIso_comp {k l m : I} (f : k ⟶ l) (g : l ⟶ m)
    (F : I ⥤ Sheaf J A) (i : Under m) :
    (J.overMapPullback A (Y.map f)).map
        ((sourceSliceChangeIso J A Y g F).hom.app i) ≫
      (sourceSliceChangeIso J A Y f F).hom.app ((Under.map g).obj i) =
    (J.overMapPullbackComp A (Y.map f) (Y.map g)).hom.app
        ((sourceSliceDiagram J A Y m F).obj i) ≫
      (J.overMapPullbackCongr A (Y.map_comp f g).symm).hom.app
        ((sourceSliceDiagram J A Y m F).obj i) ≫
      (sourceSliceChangeIso J A Y (f ≫ g) F).hom.app i := by
  ext U
  simp [sourceSliceDiagram, sourceSliceRestriction]

end Langlands.Sheaf

import Langlands.Shimura.Coefficients.EtaleTorsorPullback
import Langlands.CategoryTheory.EquivariantDiagramFunctoriality

/-! # Identity and composition of actual geometric torsor diagrams -/

noncomputable section

universe u uI vI

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (X : Scheme.{u})

/-- The first fiber projection identifies identity base change on the actual
small-etale category with the identity functor. -/
def etaleObjectPullbackId : etaleObjectPullback (𝟙 X) ≅ 𝟭 X.Etale :=
  NatIso.ofComponents
    (fun U => MorphismProperty.Over.isoMk (asIso (pullback.fst U.hom (𝟙 X)))
      (by simp [pullback.condition]))
    (by
      intro U V a
      apply MorphismProperty.Over.Hom.ext
      change ((etaleObjectPullback (𝟙 X)).map a).left ≫
          pullback.fst V.hom (𝟙 X) =
        pullback.fst U.hom (𝟙 X) ≫ a.left
      simp [etaleObjectPullback])

/-- The identity comparison is the actual first fiber projection. -/
@[simp] theorem etaleObjectPullbackId_hom_app_left (U : X.Etale) :
    ((etaleObjectPullbackId X).hom.app U).left = pullback.fst U.hom (𝟙 X) := rfl

/-- Identity base change of a cover and all deck maps is canonically the cover. -/
def etaleTorsorPullbackId (G : Type u) [Group G] :
    etaleTorsorPullbackFunctor (𝟙 X) G ≅ 𝟭 (Action X.Etale G) :=
  Functor.mapActionCongr G (etaleObjectPullbackId X)

variable {X} {Z : Scheme.{u}} (f : Z ⟶ X)
variable {I : Type uI} [Category.{vI} I] (D : I ⥤ GrpCat.{u})

/-- Identity base change of the whole varying-group torsor diagram. -/
def etaleTorsorDiagramPullbackId :
    etaleTorsorDiagramPullback (𝟙 X) D ≅ 𝟭 (EquivariantDiagram D X.Etale) :=
  EquivariantDiagram.mapFunctorCongr (etaleObjectPullbackId X) ≪≫
    EquivariantDiagram.mapFunctorId

/-- Composition base change of whole varying-group cover diagrams. -/
def etaleTorsorDiagramPullbackComp {V : Scheme.{u}} (g : V ⟶ Z) :
    etaleTorsorDiagramPullback (g ≫ f) D ≅
      etaleTorsorDiagramPullback f D ⋙ etaleTorsorDiagramPullback g D :=
  EquivariantDiagram.mapFunctorCongr
      (MorphismProperty.Over.pullbackComp g f) ≪≫
    EquivariantDiagram.mapFunctorComp (etaleObjectPullback f) (etaleObjectPullback g)

/-- At every index, identity comparison projects onto the original cover. -/
@[simp] theorem etaleTorsorDiagramPullbackId_hom_app_left
    (Y : EquivariantDiagram D X.Etale) (i : I) :
    (((etaleTorsorDiagramPullbackId D).hom.app Y).hom.app i).left =
      pullback.fst (Y.action i).V.hom (𝟙 X) := by
  change pullback.fst (Y.action i).V.hom (𝟙 X) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The composition comparison preserves the original cover coordinate. -/
@[reassoc (attr := simp)] theorem etaleTorsorDiagramPullbackComp_hom_fst_fst
    {V : Scheme.{u}} (g : V ⟶ Z) (Y : EquivariantDiagram D X.Etale) (i : I) :
    (((etaleTorsorDiagramPullbackComp f D g).hom.app Y).hom.app i).left ≫
        pullback.fst (pullback.snd (Y.action i).V.hom f) g ≫
        pullback.fst (Y.action i).V.hom f =
      pullback.fst (Y.action i).V.hom (g ≫ f) := by
  change (((MorphismProperty.Over.pullbackComp g f).hom.app (Y.action i).V).left ≫
      𝟙 _) ≫ _ ≫ _ = _
  rw [Category.comp_id]
  exact MorphismProperty.Over.pullbackComp_left_fst_fst g f (Y.action i).V

/-- The same comparison is over the unchanged new base. -/
@[reassoc (attr := simp)] theorem etaleTorsorDiagramPullbackComp_hom_snd
    {V : Scheme.{u}} (g : V ⟶ Z) (Y : EquivariantDiagram D X.Etale) (i : I) :
    (((etaleTorsorDiagramPullbackComp f D g).hom.app Y).hom.app i).left ≫
        pullback.snd (pullback.snd (Y.action i).V.hom f) g =
      pullback.snd (Y.action i).V.hom (g ≫ f) :=
  (((etaleTorsorDiagramPullbackComp f D g).hom.app Y).hom.app i).w

end Langlands.Shimura.Coefficients

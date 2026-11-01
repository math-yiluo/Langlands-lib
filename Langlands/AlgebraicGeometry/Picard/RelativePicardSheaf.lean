import Langlands.AlgebraicGeometry.Picard.RelativePicardPresheaf
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Over

/-! # The fppf relative Picard sheaf -/

universe u

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativePicard

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The ordinary relative Picard sheaf, valued in abelian groups. -/
def sheaf : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj (presheaf f)

/-- The underlying abelian-group-valued presheaf of the relative Picard sheaf. -/
def sheafPresheaf : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (sheaf f).obj

/-- The natural sheafification unit on ordinary relative Picard groups. -/
def toSheaf : presheaf f ⟶ sheafPresheaf f :=
  toSheafify (Scheme.fppfTopology.over S) (presheaf f)

/-- The ordinary relative Picard sheaf as the sheafification of class sets. -/
def classSheaf : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj (classPresheaf f)

/-- The underlying set-valued presheaf of the relative Picard class sheaf. -/
def classSheafPresheaf : (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (classSheaf f).obj

/-- The natural unit from ordinary line-bundle classes to their fppf sheafification. -/
def toClassSheaf : classPresheaf f ⟶ classSheafPresheaf f :=
  toSheafify (Scheme.fppfTopology.over S) (classPresheaf f)

lemma sheafPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (sheafPresheaf f) :=
  (sheaf f).property

lemma classSheafPresheaf_isSheaf :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (classSheafPresheaf f) :=
  (classSheaf f).property

/-- Forgetting abelian groups commutes with relative Picard sheafification. -/
def forgetSheafIso :
    sheafPresheaf f ⋙ forget AddCommGrpCat.{u + 1} ≅ classSheafPresheaf f :=
  Functor.isoWhiskerRight
      (plusPlusIsoSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}
        (presheaf f)).symm (forget AddCommGrpCat.{u + 1}) ≪≫
    (Scheme.fppfTopology.over S).sheafifyCompIso (forget AddCommGrpCat.{u + 1})
      (presheaf f) ≪≫
    plusPlusIsoSheafify (Scheme.fppfTopology.over S) (Type (u + 1)) (classPresheaf f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma toSheaf_forgetSheafIso_hom :
    whiskerRight (toSheaf f) (forget AddCommGrpCat.{u + 1}) ≫
      (forgetSheafIso f).hom = toClassSheaf f := by
  have h :
      toSheafify (Scheme.fppfTopology.over S) (presheaf f) ≫
        (plusPlusIsoSheafify (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}
          (presheaf f)).inv =
        (Scheme.fppfTopology.over S).toSheafify (presheaf f) := by
    rw [Iso.comp_inv_eq]
    exact (toSheafify_plusPlusIsoSheafify_hom _ _ _).symm
  simp only [forgetSheafIso, toSheaf, toClassSheaf, sheafPresheaf, sheaf,
    classSheafPresheaf, classSheaf, Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, ← whiskerRight_comp, h,
    GrothendieckTopology.whiskerRight_toSheafify_sheafifyCompIso_hom]
  exact toSheafify_plusPlusIsoSheafify_hom _ _ (classPresheaf f)

/-- Extend a map from the ordinary Picard presheaf to an abelian-group sheaf. -/
def lift (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})
    (η : presheaf f ⟶ F.obj) : sheafPresheaf f ⟶ F.obj :=
  sheafifyLift (Scheme.fppfTopology.over S) η F.property

@[reassoc (attr := simp)]
lemma toSheaf_lift (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})
    (η : presheaf f ⟶ F.obj) :
    toSheaf f ≫ lift f F η = η :=
  toSheafify_sheafifyLift _ _ _

lemma lift_unique (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})
    (η : presheaf f ⟶ F.obj) (γ : sheafPresheaf f ⟶ F.obj)
    (h : toSheaf f ≫ γ = η) : γ = lift f F η :=
  sheafifyLift_unique _ _ _ _ h

/-- Extend a map from ordinary line-bundle classes to any set-valued fppf sheaf. -/
def classLift (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (η : classPresheaf f ⟶ F.obj) : classSheafPresheaf f ⟶ F.obj :=
  sheafifyLift (Scheme.fppfTopology.over S) η F.property

@[reassoc (attr := simp)]
lemma toClassSheaf_classLift (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (η : classPresheaf f ⟶ F.obj) :
    toClassSheaf f ≫ classLift f F η = η :=
  toSheafify_sheafifyLift _ _ _

lemma classLift_unique (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (η : classPresheaf f ⟶ F.obj) (γ : classSheafPresheaf f ⟶ F.obj)
    (h : toClassSheaf f ≫ γ = η) : γ = classLift f F η :=
  sheafifyLift_unique _ _ _ _ h

/-- The fppf relative Picard class of an actual line bundle on `T ×_S X`. -/
def sheafClassOf (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) :
    (classSheafPresheaf f).obj (op T) :=
  (toClassSheaf f).app (op T) (classOf f T L)

@[simp]
lemma toClassSheaf_app_classOf (T : Over S)
    (L : LineBundle ((relativeSpace f).obj T)) :
    (toClassSheaf f).app (op T) (classOf f T L) = sheafClassOf f T L := rfl

@[simp]
lemma map_sheafClassOf {T U : Over S} (h : T ⟶ U)
    (L : LineBundle ((relativeSpace f).obj U)) :
    (classSheafPresheaf f).map h.op (sheafClassOf f U L) =
      sheafClassOf f T ((LineBundle.pullback ((relativeSpace f).map h)).obj L) := by
  dsimp only [sheafClassOf]
  rw [← map_classOf f h L]
  exact ((toClassSheaf f).naturality_apply h.op (classOf f U L)).symm

end Langlands.AlgebraicGeometry.Picard.RelativePicard

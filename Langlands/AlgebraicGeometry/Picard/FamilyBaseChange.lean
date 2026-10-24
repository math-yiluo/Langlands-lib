import Langlands.AlgebraicGeometry.Picard.HomFamilyPullback
import Langlands.AbelianScheme.KernelBaseChange

/-! # Actual base change of rigidified families -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

@[reassoc (attr := simp)]
lemma unitSection_baseChange_fst :
    unitSection ((baseChange b).obj A) ≫ pullback.fst A.X.hom b =
      b ≫ unitSection A := by
  have h := congrArg (fun k : (Over.map b).obj (Over.mk (𝟙 S')) ⟶ A.X ↦ k.left)
    ((GroupScheme.baseChangePointsEquiv b A.toGrp (Over.mk (𝟙 S'))).map_one)
  change unitSection ((baseChange b).obj A) ≫ pullback.fst A.X.hom b =
    (1 : (Over.map b).obj (Over.mk (𝟙 S')) ⟶ A.X).left at h
  rw [h]
  exact (congrArg (fun k : (Over.map b).obj (Over.mk (𝟙 S')) ⟶ A.X ↦ k.left)
    (MonObj.comp_one (M := A.X)
      (Over.homMk b (by simp) :
        (Over.map b).obj (Over.mk (𝟙 S')) ⟶ Over.mk (𝟙 S)))).symm

/-- The actual map from `T ×_{S'} A_{S'}` to `T ×_S A`. -/
def familyBaseChangeSpaceMap (T : Over S') :
    (relativeSpace ((baseChange b).obj A).X.hom).obj T ⟶
      (relativeSpace A.X.hom).obj ((Over.map b).obj T) :=
  pullback.lift (pullback.fst T.hom ((baseChange b).obj A).X.hom)
    (pullback.snd T.hom ((baseChange b).obj A).X.hom ≫ pullback.fst A.X.hom b)
    (by
      change pullback.fst T.hom (pullback.snd A.X.hom b) ≫ (T.hom ≫ b) = _
      rw [← Category.assoc, pullback.condition, Category.assoc,
        ← pullback.condition, ← Category.assoc]
      rfl)

@[reassoc (attr := simp)]
lemma familyBaseChangeSpaceMap_fst (T : Over S') :
    familyBaseChangeSpaceMap b A T ≫
      pullback.fst ((Over.map b).obj T).hom A.X.hom =
        pullback.fst T.hom ((baseChange b).obj A).X.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma familyBaseChangeSpaceMap_snd (T : Over S') :
    familyBaseChangeSpaceMap b A T ≫
      pullback.snd ((Over.map b).obj T).hom A.X.hom =
        pullback.snd T.hom ((baseChange b).obj A).X.hom ≫ pullback.fst A.X.hom b :=
  pullback.lift_snd _ _ _

@[simp]
lemma relativeSection_familyBaseChangeSpaceMap (T : Over S') :
    (relativeSection ((baseChange b).obj A).X.hom
      (unitSection ((baseChange b).obj A)) (unitSection_comp _)).app T ≫
        familyBaseChangeSpaceMap b A T =
      (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
        ((Over.map b).obj T) := by
  apply pullback.hom_ext
  · simp [Category.assoc, relativeSection, familyBaseChangeSpaceMap]
  · simp [Category.assoc, relativeSection, familyBaseChangeSpaceMap]

/-- Pull back the actual rigidified family across a change of the ground scheme. -/
def familyBaseChange (T : Over S') :
    RigidifiedFamily A ((Over.map b).obj T) ⥤
      RigidifiedFamily ((baseChange b).obj A) T :=
  RigidifiedLineBundle.pullback (familyBaseChangeSpaceMap b A T) (𝟙 T.left)
    (by simp)

/-- Forgetting the rigidification gives the ordinary pullback along the displayed map. -/
def familyBaseChangeForgetIso (T : Over S') :
    familyBaseChange b A T ⋙ RigidifiedLineBundle.forget _ ≅
      RigidifiedLineBundle.forget _ ⋙ LineBundle.pullback (familyBaseChangeSpaceMap b A T) :=
  Iso.refl _

end Langlands.AbelianScheme

import Langlands.AlgebraicGeometry.Picard.AffineMumfordTransport
import Langlands.AlgebraicGeometry.Picard.DualBaseChangePoincare

/-! # Ample Mumford presentations under affine change of base -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

local notation "A'" => Functor.obj (baseChange b) A
local notation "p" => pullback.fst A.X.hom b
local notation "q" => baseChangeFamilySpaceMap b A A.X

/-- The map of the actual self-products, viewed over the original base. -/
def baseChangeMumfordProductMapOver :
    (Over.map b).obj (mumfordProduct A') ⟶ mumfordProduct A :=
  Over.homMk q (by
    change q ≫ (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) =
      (pullback.fst (A').X.hom (A').X.hom ≫ (A').X.hom) ≫ b
    rw [baseChangeFamilySpaceMap_fst_assoc, Category.assoc, pullback.condition]
    rfl)

/-- The map of the actual self-products commutes with their addition maps. -/
lemma baseChangeFamilySpaceMap_addition :
    q ≫ mumfordAddition A = mumfordAddition A' ≫ p := by
  let E := GroupScheme.baseChangePointsEquiv b A.toGrp (mumfordProduct A')
  have h1 : baseChangeMumfordProductMapOver b A ≫ mumfordFirst A = E (mumfordFirst A') := by
    apply Over.OverMorphism.ext
    exact baseChangeFamilySpaceMap_fst b A A.X
  have h2 : baseChangeMumfordProductMapOver b A ≫ mumfordSecond A = E (mumfordSecond A') := by
    apply Over.OverMorphism.ext
    exact baseChangeFamilySpaceMap_snd b A A.X
  have h : baseChangeMumfordProductMapOver b A ≫ (mumfordFirst A * mumfordSecond A) =
      E (mumfordFirst A' * mumfordSecond A') := by
    rw [MonObj.comp_mul, h1, h2, map_mul]
  exact congrArg (fun f => f.left) h

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})

/-- Base change of the ordinary line bundle underlying unit normalization. -/
def baseChangeNormalizedBundleIso (L : LineBundle A.X.left) (B : LineBundle S) :
    (LineBundle.pullback p).obj
        (LineBundle.tensor preservation L ((LineBundle.pullback A.X.hom).obj B)) ≅
      LineBundle.tensor preservation ((LineBundle.pullback p).obj L)
        ((LineBundle.pullback (A').X.hom).obj ((LineBundle.pullback b).obj B)) :=
  LineBundle.pullbackTensorObjIso preservation p L _ ≪≫
    LineBundle.tensorIso preservation (Iso.refl _)
      (LineBundle.pullbackCompEqIso p A.X.hom pullback.condition B ≪≫
        (LineBundle.pullbackCompEqIso (A').X.hom b rfl B).symm)

/-- The actual unit evaluation pulled back to the new base. -/
def baseChangeUnitEvaluation (L : LineBundle A.X.left) (B : LineBundle S)
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf S) :
    tensorObj ((Scheme.Modules.pullback (unitSection A')).obj
        ((LineBundle.pullback p).obj L).obj) ((LineBundle.pullback b).obj B).obj ≅
      structureSheaf S' :=
  (Langlands.Scheme.Modules.tensorFunctor S').mapIso
      (((Scheme.Modules.pullbackComp (unitSection A') p).app L.obj ≪≫
        (Scheme.Modules.pullbackCongr (unitSection_baseChange_fst b A)).app L.obj ≪≫
        ((Scheme.Modules.pullbackComp b (unitSection A)).app L.obj).symm).prod (Iso.refl _)) ≪≫
    pullbackTensorEvaluation preservation b _ _ evaluationB

/-- The actual normalized inverse evaluation pulled back to the total space. -/
def baseChangeNormalizedEvaluation (L : LineBundle A.X.left) (B : LineBundle S)
    (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection A)).obj L.obj) B.obj ≅
      structureSheaf S)
    (M : LineBundle A.X.left)
    (evaluation : tensorObj
      (LineBundle.normalize preservation A.X.hom (unitSection A) (unitSection_comp A)
        L B evaluationB).obj.carrier M.obj ≅ structureSheaf A.X.left) :
    tensorObj
      (LineBundle.normalize preservation (A').X.hom (unitSection A') (unitSection_comp A')
        ((LineBundle.pullback p).obj L) ((LineBundle.pullback b).obj B)
        (baseChangeUnitEvaluation b A preservation L B evaluationB)).obj.carrier
      ((LineBundle.pullback p).obj M).obj ≅ structureSheaf (A').X.left :=
  (Langlands.Scheme.Modules.tensorFunctor (A').X.left).mapIso
      (((LineBundle.forget _).mapIso
        (baseChangeNormalizedBundleIso b A preservation L B)).symm.prod (Iso.refl _)) ≪≫
    pullbackTensorEvaluation preservation p _ _ evaluation

/-- Pullback of the three actual tensor factors underlying the Mumford family. -/
def baseChangeMumfordBundleIso (L : LineBundle A.X.left) (B : LineBundle S)
    (M : LineBundle A.X.left) :
    (LineBundle.pullback q).obj
        (LineBundle.tensor preservation
          (LineBundle.tensor preservation
            ((LineBundle.pullback (mumfordAddition A)).obj
              (LineBundle.tensor preservation L ((LineBundle.pullback A.X.hom).obj B)))
            ((LineBundle.pullback (pullback.fst A.X.hom A.X.hom)).obj M))
          ((LineBundle.pullback (pullback.snd A.X.hom A.X.hom)).obj M)) ≅
      LineBundle.tensor preservation
        (LineBundle.tensor preservation
          ((LineBundle.pullback (mumfordAddition A')).obj
            (LineBundle.tensor preservation ((LineBundle.pullback p).obj L)
              ((LineBundle.pullback (A').X.hom).obj ((LineBundle.pullback b).obj B))))
          ((LineBundle.pullback (pullback.fst (A').X.hom (A').X.hom)).obj
            ((LineBundle.pullback p).obj M)))
        ((LineBundle.pullback (pullback.snd (A').X.hom (A').X.hom)).obj
          ((LineBundle.pullback p).obj M)) :=
  LineBundle.pullbackTensorObjIso preservation _ _ _ ≪≫
    LineBundle.tensorIso preservation
      (LineBundle.pullbackTensorObjIso preservation _ _ _ ≪≫
        LineBundle.tensorIso preservation
          (LineBundle.pullbackCompEqIso _ _ (baseChangeFamilySpaceMap_addition b A) _ ≪≫
            (LineBundle.pullbackCompEqIso _ _ rfl _).symm ≪≫
            (LineBundle.pullback (mumfordAddition A')).mapIso
              (baseChangeNormalizedBundleIso b A preservation L B))
          (LineBundle.pullbackCompEqIso _ _ (baseChangeFamilySpaceMap_fst b A A.X) _ ≪≫
            (LineBundle.pullbackCompEqIso _ _ rfl _).symm))
      (LineBundle.pullbackCompEqIso _ _ (baseChangeFamilySpaceMap_snd b A A.X) _ ≪≫
        (LineBundle.pullbackCompEqIso _ _ rfl _).symm)

variable (square : MumfordBundlePicardZeroStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u}) (hA : HasDualScheme A)

/-- An ample presentation remains ample after affine base change, using the actual
canonical comparison of dual schemes. -/
theorem hasAmpleMumfordPresentation_baseChange [IsAffineHom b]
    (f : A.X ⟶ dualScheme A hA)
    (h : HasAmpleMumfordPresentation preservation square A hA f) :
    HasAmpleMumfordAfterBaseChange preservation square A hA universality b f := by
  let : IsAffineHom p := MorphismProperty.pullback_fst A.X.hom b inferInstance
  let e := dualBaseChangeMapPoincareForgetIso b universality A hA f
  obtain ⟨L, B, evaluationB, M, evaluation, hL, rfl⟩ := h
  let evaluationB' := baseChangeUnitEvaluation b A preservation L B evaluationB
  let evaluation' := baseChangeNormalizedEvaluation b A preservation L B evaluationB M evaluation
  refine ⟨(LineBundle.pullback p).obj L, (LineBundle.pullback b).obj B, evaluationB',
    (LineBundle.pullback p).obj M, evaluation', affinePullbackAmple p L hL, ?_⟩
  rw [eq_mumfordSchemeMapOfLineBundle_iff]
  exact RigidifiedLineBundle.nonempty_iso_of_forget_iso preservation
    ((relativeProjection (A').X.hom).app (A').X)
    (relativeSection_projection (A').X.hom (unitSection A') (unitSection_comp A') (A').X)
    (e ≪≫ (LineBundle.pullback q).mapIso
      ((RigidifiedLineBundle.forget _).mapIso
        (mumfordSchemeMapOfLineBundlePullbackIso preservation A L B evaluationB M evaluation
          square hA) ≪≫
        eqToIso (mumfordFamilyOfLineBundle_forget preservation A L B evaluationB M evaluation)) ≪≫
      baseChangeMumfordBundleIso b A preservation L B M ≪≫
      eqToIso (mumfordFamilyOfLineBundle_forget preservation A' _ _ evaluationB' _ evaluation').symm)

end Langlands.AbelianScheme

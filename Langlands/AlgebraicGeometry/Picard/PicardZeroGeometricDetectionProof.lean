import Langlands.AlgebraicGeometry.Picard.PicardZeroGeometricDetectionStatement
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Picard.TranslationBaseChange
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Geometric-point detection for actual rigidified Picard-zero families -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)
  {V : Scheme.{u}} (s : V ⟶ T.left)

private lemma geometricPointComparison_relative_map :
    (GroupScheme.baseChangeCompIso T.hom s A.toGrp).inv.hom.hom.left ≫
        (relativeSpaceSymmetry A.X.hom (Over.mk (s ≫ T.hom))).inv ≫
          (relativeSpace A.X.hom).map (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T) =
      pullback.fst (pullback.snd A.X.hom T.hom) s ≫
        (relativeSpaceSymmetry A.X.hom T).inv := by
  have hw : (GroupScheme.baseChangeCompIso T.hom s A.toGrp).inv.hom.hom.left ≫
      pullback.snd A.X.hom (s ≫ T.hom) =
      pullback.snd (pullback.snd A.X.hom T.hom) s :=
    (GroupScheme.baseChangeCompIso T.hom s A.toGrp).inv.hom.hom.w
  apply pullback.hom_ext
  · simp only [relativeSpaceSymmetry, relativeSpace, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left, Category.assoc, pullback.lift_fst,
      pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_fst_assoc]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ s) hw).trans
        (pullback.condition (f := pullback.snd A.X.hom T.hom) (g := s)).symm)
  · simp only [relativeSpaceSymmetry, relativeSpace, Functor.comp_map, Over.forget_map,
      Over.pullback_map_left, Category.assoc, pullback.lift_snd,
      pullbackSymmetry_inv_comp_snd]
    exact GroupScheme.baseChangeCompIso_inv_fst T.hom s A.toGrp

/-- The direct geometric-point family and the original fibre have the same bundle
under the actual group-scheme composition comparison. -/
def geometricPointPullbackLineBundleIso (L : RigidifiedFamily A T) :
    (LineBundle.pullback
      (GroupScheme.baseChangeCompIso T.hom s A.toGrp).inv.hom.hom.left).obj
        (familyLineBundle A
          ((RigidifiedLineBundle.relativePullback A.X.hom
            (unitSection A) (unitSection_comp A)
            (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T)).obj L)) ≅
      fibreLineBundle ((baseChange T.hom).obj A) (familyLineBundle A L) s := by
  let N := (RigidifiedLineBundle.forget _).obj L
  let e := (GroupScheme.baseChangeCompIso T.hom s A.toGrp).inv.hom.hom.left
  let a := (relativeSpaceSymmetry A.X.hom (Over.mk (s ≫ T.hom))).inv
  let r := (relativeSpace A.X.hom).map
    (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T)
  let p := pullback.fst (pullback.snd A.X.hom T.hom) s
  let b := (relativeSpaceSymmetry A.X.hom T).inv
  change (LineBundle.pullback e).obj
      ((LineBundle.pullback a).obj ((LineBundle.pullback r).obj N)) ≅
    (LineBundle.pullback p).obj ((LineBundle.pullback b).obj N)
  exact (LineBundle.pullback e).mapIso ((LineBundle.pullbackComp a r).app N) ≪≫
    (LineBundle.pullbackComp e (a ≫ r)).app N ≪≫
    eqToIso (congrArg (fun f ↦ (LineBundle.pullback f).obj N)
      (geometricPointComparison_relative_map A T s)) ≪≫
    ((LineBundle.pullbackComp p b).app N).symm

/-- Actual rigidified relative pullbacks to all geometric points detect Picard zero. -/
theorem picardZeroGeometricDetection : PicardZeroGeometricDetectionStatement.{u} := by
  intro S A T L
  constructor
  · intro hL K _ _ s
    exact picardZeroPullback S A _ T
      (Over.homMk s rfl : Over.mk (s ≫ T.hom) ⟶ T) L hL
  · intro hL K _ _ s
    have h := isTranslationInvariant_of_isGeometricallyPicardZero K
      ((baseChange (s ≫ T.hom)).obj A) (hL K s)
    exact GroupScheme.isTranslationInvariant_of_iso _
      (geometricPointPullbackLineBundleIso A T s L)
      (GroupScheme.isTranslationInvariant_pullback
        (GroupScheme.baseChangeCompIso T.hom s A.toGrp).inv h)

end Langlands.AbelianScheme

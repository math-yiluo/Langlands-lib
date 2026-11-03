import Langlands.AlgebraicGeometry.ProjectiveBundle.FrameChoice
import Langlands.AlgebraicGeometry.ProjectiveBundle.Tautological
import Langlands.AlgebraicGeometry.Modules.CommonSourceTransitionTransport
import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr

/-! # Degree-one line bundles under changes of genuine frames -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.RelativeProjectiveSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Scheme.Modules

/-- A composition comparison over an identity map is the canonical identity pullback. -/
lemma compIso_id_left_congr {X Y : Scheme.{u}} (a : X ⟶ X) (b : X ⟶ Y)
    (ha : a = 𝟙 X) (hab : a ≫ b = b) (N : Y.Modules) :
    compIso a b b hab N =
      (Scheme.Modules.pullbackCongr ha).app ((Scheme.Modules.pullback b).obj N) ≪≫
        (Scheme.Modules.pullbackId X).app ((Scheme.Modules.pullback b).obj N) := by
  subst a
  apply Iso.ext
  rw [compIso_hom, compHom_id_left]
  simp [Scheme.Modules.pullbackCongr]

end Langlands.Scheme.Modules


namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}

/-- The concrete dual-frame coordinate change on one frame-bearing open. -/
abbrev familyCoordinate (b c : FrameFamily M n) (U : FrameOpen M n) :=
  coordinatesOnOpen n U.val ((b U).dual.change (c U).dual U.val le_rfl le_rfl)

lemma familyCoordinate_trans (b c d : FrameFamily M n) (U : FrameOpen M n) :
    (familyCoordinate b c U).trans (familyCoordinate c d U) = familyCoordinate b d U := by
  dsimp only [familyCoordinate, coordinatesOnOpen]
  rw [← ProjectiveSpace.coordinateBaseChange_trans, LocalFrame.change_trans]

/-- The chart actions compose according to the actual changes of dual frames. -/
lemma familyLinearAction_comp (b c d : FrameFamily M n) (U : FrameOpen M n) :
    globalLinearAction n (familyCoordinate b c U) ≫
        globalLinearAction n (familyCoordinate c d U) =
      globalLinearAction n (familyCoordinate b d U) := by
  rw [globalLinearAction_comp, familyCoordinate_trans]

variable (hM : IsLocallyFreeOfRank M (n + 1))

/-- The maps associated to genuine frame changes compose. -/
lemma frameChoiceIso_hom_comp (b c d : FrameFamily M n) :
    (frameChoiceIso hM b c).hom ≫ (frameChoiceIso hM c d).hom =
      (frameChoiceIso hM b d).hom :=
  congrArg Iso.hom (frameChoiceIso_trans hM b c d)

/-- The existing family comparison factors its map to the fixed frame bundle. -/
lemma frameChoiceIso_hom_toFrameBundle (b c : FrameFamily M n) :
    (frameChoiceIso hM b c).hom ≫ (toFrameBundleIso hM c).hom =
      (toFrameBundleIso hM b).hom :=
  congrArg Iso.hom (frameChoiceIso_trans hM b c (frame M n))

/-- The actual degree-one line bundle on a genuine frame-family construction. -/
def familyTwistOne (b : FrameFamily M n) : LineBundle (familyBundle hM b) :=
  ⟨(Scheme.Modules.pullback (toFrameBundleIso hM b).hom).obj (FrameBundle.twistOne hM).obj,
    (FrameBundle.twistOne hM).property.pullback (toFrameBundleIso hM b).hom⟩

/-- The degree-one module is preserved by the actual change of frame families. -/
def frameChoiceTwistIso (b c : FrameFamily M n) :
    (Scheme.Modules.pullback (frameChoiceIso hM b c).hom).obj (familyTwistOne hM c).obj ≅
      (familyTwistOne hM b).obj :=
  compIso (frameChoiceIso hM b c).hom (toFrameBundleIso hM c).hom
    (toFrameBundleIso hM b).hom (frameChoiceIso_hom_toFrameBundle hM b c)
    (FrameBundle.twistOne hM).obj

/-- The corresponding comparison is an isomorphism of actual line bundles. -/
def frameChoiceTwistLineIso (b c : FrameFamily M n) :
    (LineBundle.pullback (frameChoiceIso hM b c).hom).obj (familyTwistOne hM c) ≅
      familyTwistOne hM b :=
  ObjectProperty.isoMk _ (frameChoiceTwistIso hM b c)

/-- Global degree-one frame comparisons satisfy canonical pullback composition. -/
lemma frameChoiceTwistIso_comp (b c d : FrameFamily M n) :
    (Scheme.Modules.pullback (frameChoiceIso hM b c).hom).map
        (compIso (frameChoiceIso hM c d).hom (toFrameBundleIso hM d).hom
          (toFrameBundleIso hM c).hom (frameChoiceIso_hom_toFrameBundle hM c d)
          (FrameBundle.twistOne hM).obj).hom ≫
      (compIso (frameChoiceIso hM b c).hom (toFrameBundleIso hM c).hom
        (toFrameBundleIso hM b).hom (frameChoiceIso_hom_toFrameBundle hM b c)
        (FrameBundle.twistOne hM).obj).hom =
      compHom (frameChoiceIso hM b c).hom (frameChoiceIso hM c d).hom
          (frameChoiceIso hM b d).hom
          (frameChoiceIso_hom_comp hM b c d)
          ((Scheme.Modules.pullback (toFrameBundleIso hM d).hom).obj
            (FrameBundle.twistOne hM).obj) ≫
        (compIso (frameChoiceIso hM b d).hom (toFrameBundleIso hM d).hom
          (toFrameBundleIso hM b).hom (frameChoiceIso_hom_toFrameBundle hM b d)
          (FrameBundle.twistOne hM).obj).hom := by
  simpa only [compIso_hom] using (LineBundleFlatDescent.compIso_assoc
    (frameChoiceIso hM b c).hom (frameChoiceIso hM c d).hom
    (toFrameBundleIso hM d).hom (frameChoiceIso hM b d).hom
    (toFrameBundleIso hM c).hom (toFrameBundleIso hM b).hom
    (frameChoiceIso_hom_comp hM b c d)
    (frameChoiceIso_hom_toFrameBundle hM c d)
    (frameChoiceIso_hom_toFrameBundle hM b c)
    (frameChoiceIso_hom_toFrameBundle hM b d) (FrameBundle.twistOne hM).obj).symm


/-- At identical frame families, the comparison is the canonical identity pullback. -/
lemma frameChoiceTwistIso_refl (b : FrameFamily M n) :
    frameChoiceTwistIso hM b b =
      (Scheme.Modules.pullbackCongr
          (congrArg Iso.hom (frameChoiceIso_refl hM b))).app (familyTwistOne hM b).obj ≪≫
        (Scheme.Modules.pullbackId (familyBundle hM b)).app (familyTwistOne hM b).obj := by
  exact compIso_id_left_congr (frameChoiceIso hM b b).hom
    (toFrameBundleIso hM b).hom (congrArg Iso.hom (frameChoiceIso_refl hM b))
    (frameChoiceIso_hom_toFrameBundle hM b b) (FrameBundle.twistOne hM).obj

/-- The family-chart map to the fixed bundle uses the actual dual-frame action. -/
lemma familyChart_toFrameBundle (b : FrameFamily M n) (U : FrameOpen M n) :
    (familyCocycle hM b).chart U ≫ (toFrameBundleIso hM b).hom =
      globalLinearAction n (familyCoordinate b (frame M n) U) ≫ FrameBundle.chart hM U :=
  chart_frameChoiceIso_hom hM b (frame M n) U

/-- The transported degree-one bundle has the actual standard twist on every chart. -/
def familyTwistChartIso (b : FrameFamily M n) (U : FrameOpen M n) :
    (Scheme.Modules.pullback ((familyCocycle hM b).chart U)).obj
        (familyTwistOne hM b).obj ≅ (RelativeProjectiveSpace.twistOne U.val.toScheme n).obj :=
  squarePullbackIso (FrameBundle.chart hM U) ((familyCocycle hM b).chart U)
      (globalLinearAction n (familyCoordinate b (frame M n) U))
      (toFrameBundleIso hM b).hom (familyChart_toFrameBundle hM b U)
      (FrameBundle.twistOne hM).obj ≪≫
    (Scheme.Modules.pullback (globalLinearAction n (familyCoordinate b (frame M n) U))).mapIso
      (FrameBundle.twistOneModuleIso hM U) ≪≫
    LinearSystem.globalLinearActionTwistIso U.val.toScheme n (familyCoordinate b (frame M n) U)

end Langlands.AlgebraicGeometry.ProjectiveBundle

import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationGeneration
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed immersion of projective evaluation from its actual local maps -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {X S : Scheme.{u}} (p : X ⟶ S) {M : S.Modules} (L : LineBundle X)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj) {n : ℕ}
    (hM : IsLocallyFreeOfRank M (n + 1)) (hs : FrameEvaluationGenerates p L ev n)

/-- Each actual local evaluation is the Cartesian restriction of global evaluation
to the corresponding projective frame chart. -/
lemma isPullback_evaluationMap_chart (U : FrameOpen M n) :
    IsPullback (p ⁻¹ᵁ U.val).ι
      (localEvaluationMap p L ev (frame M n U) U.val le_rfl (hs U))
      (evaluationMap p L ev hM hs) (FrameBundle.chart hM U) := by
  have houter : IsPullback
      (localEvaluationMap p L ev (frame M n U) U.val le_rfl (hs U) ≫
        RelativeProjectiveSpace.toBase U.val.toScheme n)
      (p ⁻¹ᵁ U.val).ι U.val.ι
      (evaluationMap p L ev hM hs ≫ FrameBundle.toBase hM) := by
    simpa only [localEvaluationMap_toBase, evaluationMap_toBase,
      evaluationBase, Scheme.Hom.resLE_eq_morphismRestrict] using
        isPullback_morphismRestrict p U.val
  exact (houter.of_right (evaluationMap_chart p L ev hM hs U).symm
    (FrameBundle.isPullback_chart hM U)).flip

/-- The actual inverse-image open is canonically isomorphic to the categorical
pullback of global evaluation along its projective frame chart. -/
def evaluationChartPullbackIso (U : FrameOpen M n) :
    (p ⁻¹ᵁ U.val).toScheme ≅
      pullback (evaluationMap p L ev hM hs) (FrameBundle.chart hM U) :=
  (isPullback_evaluationMap_chart p L ev hM hs U).isoPullback

@[reassoc (attr := simp)]
lemma evaluationChartPullbackIso_hom_fst (U : FrameOpen M n) :
    (evaluationChartPullbackIso p L ev hM hs U).hom ≫ pullback.fst _ _ =
      (p ⁻¹ᵁ U.val).ι :=
  (isPullback_evaluationMap_chart p L ev hM hs U).isoPullback_hom_fst

@[reassoc (attr := simp)]
lemma evaluationChartPullbackIso_hom_snd (U : FrameOpen M n) :
    (evaluationChartPullbackIso p L ev hM hs U).hom ≫ pullback.snd _ _ =
      localEvaluationMap p L ev (frame M n U) U.val le_rfl (hs U) :=
  (isPullback_evaluationMap_chart p L ev hM hs U).isoPullback_hom_snd

/-- Every target-local morphism property of global evaluation is detected
by all actual local frame evaluations. -/
lemma evaluationMap_property_iff (Q : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget Q] :
    Q (evaluationMap p L ev hM hs) ↔
      ∀ U : FrameOpen M n,
        Q (localEvaluationMap p L ev (frame M n U) U.val le_rfl (hs U)) := by
  refine ⟨fun h U =>
    IsZariskiLocalAtTarget.of_isPullback
      (isPullback_evaluationMap_chart p L ev hM hs U) h, ?_⟩
  intro h
  apply IsZariskiLocalAtTarget.of_openCover (FrameBundle.openCover hM)
  intro U
  change Q (pullback.snd (evaluationMap p L ev hM hs) (FrameBundle.chart hM U))
  rw [← (isPullback_evaluationMap_chart p L ev hM hs U).isoPullback_inv_snd,
    Q.cancel_left_of_respectsIso]
  exact h U

/-- Global evaluation is a closed immersion exactly when its actual local
frame evaluations are closed immersions. -/
lemma isClosedImmersion_evaluationMap_iff :
    IsClosedImmersion (evaluationMap p L ev hM hs) ↔
      ∀ U : FrameOpen M n,
        IsClosedImmersion
          (localEvaluationMap p L ev (frame M n U) U.val le_rfl (hs U)) :=
  evaluationMap_property_iff p L ev hM hs @IsClosedImmersion

/-- Intrinsic generation and closed immersion on every local frame give
the actual global closed embedding. -/
lemma isClosedImmersion_evaluationMap_of_evaluationGenerates
    (hgen : EvaluationGenerates p L ev)
    (hclosed : ∀ U : FrameOpen M n,
      IsClosedImmersion (localEvaluationMap p L ev (frame M n U) U.val le_rfl
        (hgen.frameEvaluationGenerates p L ev U))) :
    IsClosedImmersion
      (evaluationMap p L ev hM (hgen.frameEvaluationGenerates p L ev)) :=
  (isClosedImmersion_evaluationMap_iff p L ev hM
    (hgen.frameEvaluationGenerates p L ev)).mpr hclosed

end Langlands.AlgebraicGeometry.ProjectiveBundle

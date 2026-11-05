import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationGluing
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.Geometry

/-! # Properness of actual frame projective bundles and evaluation maps -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

universe u

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {S : Scheme.{u}} {M : S.Modules} {n : ℕ}
    (hM : IsLocallyFreeOfRank M (n + 1))

/-- A target-local property of the structure map is detected on the actual
relative projective charts over all frame-bearing base opens. -/
lemma FrameBundle.toBase_property_iff (Q : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget Q] :
    Q (FrameBundle.toBase hM) ↔
      ∀ U : FrameOpen M n, Q (RelativeProjectiveSpace.toBase U.val.toScheme n) := by
  constructor
  · intro h U
    exact IsZariskiLocalAtTarget.of_isPullback (FrameBundle.isPullback_chart hM U).flip h
  · intro h
    apply IsZariskiLocalAtTarget.of_openCover (frameCover M n hM)
    intro U
    change Q (pullback.snd (FrameBundle.toBase hM) U.val.ι)
    rw [← (FrameBundle.isPullback_chart hM U).flip.isoPullback_inv_snd,
      Q.cancel_left_of_respectsIso]
    exact h U

/-- Glued frame projective bundles are proper over their original base. -/
instance FrameBundle.isProper_toBase : IsProper (FrameBundle.toBase hM) :=
  (FrameBundle.toBase_property_iff hM @IsProper).mpr (fun _ => inferInstance)

/-- The actual glued projective bundle, bundled as a proper scheme over its
original base. -/
def FrameBundle.properOver : { Y : Over S // IsProper Y.hom } :=
  ⟨Over.mk (FrameBundle.toBase hM), FrameBundle.isProper_toBase hM⟩

variable {X : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj)
    (hs : FrameEvaluationGenerates p L ev n)

/-- Evaluation from an actual proper source is proper, because the frame
projective bundle is separated over the same base. -/
instance isProper_evaluationMap [IsProper p] :
    IsProper (evaluationMap p L ev hM hs) := by
  have : IsProper (evaluationMap p L ev hM hs ≫ FrameBundle.toBase hM) := by
    rw [evaluationMap_toBase]
    infer_instance
  exact IsProper.of_comp _ (FrameBundle.toBase hM)

end Langlands.AlgebraicGeometry.ProjectiveBundle

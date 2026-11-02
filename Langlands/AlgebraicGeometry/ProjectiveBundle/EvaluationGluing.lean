import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationRestriction
import Mathlib.AlgebraicGeometry.Cover.Directed

/-! # Gluing actual projective evaluation morphisms -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.ProjectiveBundle

variable {X S : Scheme.{u}} (p : X ⟶ S) {M : S.Modules} (L : LineBundle X)
    (ev : M ⟶ (Scheme.Modules.pushforward p).obj L.obj) {n : ℕ}

/-- The actual evaluated sections of every chosen frame generate pointwise. -/
def FrameEvaluationGenerates (n : ℕ) : Prop :=
  ∀ U : FrameOpen M n, ∀ x : (p ⁻¹ᵁ U.val).toScheme, ∃ i,
    x ∈ nonvanishingLocus (evaluationLineBundle p L U.val).obj
      (localEvaluationSections p L ev (frame M n U) U.val le_rfl i)

/-- The actual evaluation map over a frame open, viewed in the glued frame bundle. -/
def evaluationChartMap (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) (U : FrameOpen M n) :
    (p ⁻¹ᵁ U.val).toScheme ⟶ frameBundle M n hM :=
  localEvaluationMap p L ev (frame M n U) U.val le_rfl (hs U) ≫
    FrameBundle.chart hM U

/-- Actual section and frame compatibility gives compatible maps to the frame bundle. -/
lemma evaluationChartMap_restrict (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) {U V : FrameOpen M n} (hUV : U ≤ V) :
    X.homOfLE (p.preimage_mono hUV) ≫ evaluationChartMap p L ev hM hs V =
      evaluationChartMap p L ev hM hs U := by
  dsimp only [evaluationChartMap]
  rw [← Category.assoc, ← localEvaluationMap_restrict p L ev (frame M n V)
    hUV le_rfl (hs V)]
  rw [← localEvaluationMap_change p L ev (frame M n U) (frame M n V)
    le_rfl hUV (hs U)]
  simp only [Category.assoc, FrameBundle.transition_chart]

/-- The directed frame cover pulled back along the actual structure map. -/
abbrev evaluationCover (hM : IsLocallyFreeOfRank M (n + 1)) : X.OpenCover :=
  (frameCover M n hM).pullback₁ p

/-- Its transition is the actual inverse-image-open inclusion under the canonical isos. -/
lemma evaluationCover_trans (hM : IsLocallyFreeOfRank M (n + 1))
    {U V : FrameOpen M n} (hUV : U ⟶ V) :
    (pullbackRestrictIsoRestrict p U.val).inv ≫
        (evaluationCover p hM).trans hUV ≫
        (pullbackRestrictIsoRestrict p V.val).hom =
      X.homOfLE (p.preimage_mono (show U.val ≤ V.val from leOfHom hUV)) := by
  apply (cancel_mono (p ⁻¹ᵁ V.val).ι).mp
  simp only [Category.assoc, pullbackRestrictIsoRestrict_hom_ι, Scheme.homOfLE_ι]
  change (pullbackRestrictIsoRestrict p U.val).inv ≫
      (evaluationCover p hM).trans hUV ≫ (evaluationCover p hM).f V = _
  rw [(evaluationCover p hM).trans_map hUV]
  exact pullbackRestrictIsoRestrict_inv_fst p U.val

/-- The actual evaluated map on a component of the categorical pullback cover. -/
def evaluationCoverMap (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) (U : FrameOpen M n) :
    (evaluationCover p hM).X U ⟶ frameBundle M n hM :=
  (pullbackRestrictIsoRestrict p U.val).hom ≫ evaluationChartMap p L ev hM hs U

/-- The cover-component maps agree under every directed transition. -/
lemma evaluationCoverMap_compatible (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) {U V : FrameOpen M n} (hUV : U ⟶ V) :
    (evaluationCover p hM).trans hUV ≫ evaluationCoverMap p L ev hM hs V =
      evaluationCoverMap p L ev hM hs U := by
  apply (cancel_epi (pullbackRestrictIsoRestrict p U.val).inv).mp
  dsimp only [evaluationCoverMap]
  calc
    (pullbackRestrictIsoRestrict p U.val).inv ≫
        ((evaluationCover p hM).trans hUV ≫
          (pullbackRestrictIsoRestrict p V.val).hom ≫
            evaluationChartMap p L ev hM hs V) =
        ((pullbackRestrictIsoRestrict p U.val).inv ≫
          (evaluationCover p hM).trans hUV ≫
            (pullbackRestrictIsoRestrict p V.val).hom) ≫
              evaluationChartMap p L ev hM hs V := by simp only [Category.assoc]
    _ = X.homOfLE (p.preimage_mono (show U.val ≤ V.val from leOfHom hUV)) ≫
        evaluationChartMap p L ev hM hs V := by rw [evaluationCover_trans]
    _ = evaluationChartMap p L ev hM hs U :=
      evaluationChartMap_restrict p L ev hM hs (leOfHom hUV)
    _ = _ := by simp

/-- Glue the actual frame evaluations to a morphism into the projective bundle. -/
def evaluationMap (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) : X ⟶ frameBundle M n hM :=
  (evaluationCover p hM).glueMorphismsOfLocallyDirected
    (evaluationCoverMap p L ev hM hs)
    (evaluationCoverMap_compatible p L ev hM hs)

@[reassoc (attr := simp)]
lemma evaluationMap_cover (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) (U : FrameOpen M n) :
    (evaluationCover p hM).f U ≫ evaluationMap p L ev hM hs =
      evaluationCoverMap p L ev hM hs U :=
  (evaluationCover p hM).map_glueMorphismsOfLocallyDirected _ _ U

/-- On an actual inverse-image open, the glued map is the actual local evaluation. -/
@[reassoc (attr := simp)]
lemma evaluationMap_chart (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) (U : FrameOpen M n) :
    (p ⁻¹ᵁ U.val).ι ≫ evaluationMap p L ev hM hs =
      evaluationChartMap p L ev hM hs U := by
  rw [← pullbackRestrictIsoRestrict_inv_fst p U.val, Category.assoc]
  change (pullbackRestrictIsoRestrict p U.val).inv ≫
    ((evaluationCover p hM).f U ≫ evaluationMap p L ev hM hs) = _
  rw [evaluationMap_cover]
  simp [evaluationCoverMap]

@[reassoc (attr := simp)]
lemma evaluationChartMap_toBase (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) (U : FrameOpen M n) :
    evaluationChartMap p L ev hM hs U ≫ FrameBundle.toBase hM =
      (p ⁻¹ᵁ U.val).ι ≫ p := by
  simp only [evaluationChartMap, Category.assoc, FrameBundle.chart_toBase,
    localEvaluationMap_toBase_assoc]
  exact Scheme.Hom.resLE_comp_ι _ _

/-- The glued evaluation is an actual morphism over the original base. -/
@[reassoc (attr := simp)]
lemma evaluationMap_toBase (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) :
    evaluationMap p L ev hM hs ≫ FrameBundle.toBase hM = p := by
  apply (evaluationCover p hM).hom_ext
  intro U
  simp only [evaluationMap_cover_assoc, evaluationCoverMap, Category.assoc,
    evaluationChartMap_toBase, pullbackRestrictIsoRestrict_hom_ι_assoc]
  rfl

/-- The actual local chart equations uniquely characterize the glued evaluation. -/
lemma evaluationMap_unique (hM : IsLocallyFreeOfRank M (n + 1))
    (hs : FrameEvaluationGenerates p L ev n) (f : X ⟶ frameBundle M n hM)
    (hf : ∀ U : FrameOpen M n,
      (p ⁻¹ᵁ U.val).ι ≫ f = evaluationChartMap p L ev hM hs U) :
    f = evaluationMap p L ev hM hs := by
  apply (evaluationCover p hM).hom_ext
  intro U
  rw [evaluationMap_cover]
  change (Limits.pullback.fst p U.val.ι) ≫ f = _
  rw [← pullbackRestrictIsoRestrict_hom_ι p U.val, Category.assoc, hf]
  rfl

end Langlands.AlgebraicGeometry.ProjectiveBundle

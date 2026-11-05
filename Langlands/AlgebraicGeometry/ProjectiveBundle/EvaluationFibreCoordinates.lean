import Langlands.AlgebraicGeometry.ProjectiveBundle.Fibres
import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationBaseChange

/-! # Actual evaluation coordinates on residue-field fibres -/

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
    (hM : IsLocallyFreeOfRank M (n + 1)) (hgen : FrameEvaluationGenerates p L ev n)

/-- Pullback of the actual local frame sections gives the changed evaluation map. -/
lemma evaluationMap_chartBaseChange {T Y : Scheme.{u}}
    (U : FrameOpen M n) (b : T ⟶ U.val.toScheme)
    (r : Y ⟶ T) (q : Y ⟶ (p ⁻¹ᵁ U.val).toScheme)
    (w : q ≫ evaluationBase p U.val = r ≫ b) :
    relativeLinearSystemMap r (pullbackSections_generate q (hgen U)) ≫
        FrameBundle.chartBaseChangeMap hM U b =
      q ≫ (p ⁻¹ᵁ U.val).ι ≫ evaluationMap p L ev hM hgen := by
  dsimp only [FrameBundle.chartBaseChangeMap]
  rw [← Category.assoc,
    relativeLinearSystemMap_pullback (evaluationBase p U.val) r q b w (hgen U)]
  simp only [Category.assoc, evaluationMap_chart, evaluationChartMap, localEvaluationMap]

/-- The actual source-fibre inclusion factors through the inverse-image frame open. -/
def fibreSourceLift (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    p.fiber s ⟶ (p ⁻¹ᵁ U.val).toScheme :=
  IsOpenImmersion.lift (p ⁻¹ᵁ U.val).ι (p.fiberι s) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change p (p.fiberι s z) ∈ U.val
    have hz : p (p.fiberι s z) = s := by
      rw [← Scheme.Hom.comp_apply, p.fiber_fac]
      exact Scheme.fromSpecResidueField_apply s _
    rw [hz]
    exact hs)

@[reassoc (attr := simp)]
lemma fibreSourceLift_ι (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    fibreSourceLift p U s hs ≫ (p ⁻¹ᵁ U.val).ι = p.fiberι s :=
  IsOpenImmersion.lift_fac _ _ _

/-- The source lift and original residue-point lift form the actual scalar square. -/
lemma fibreSourceLift_toBase (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    fibreSourceLift p U s hs ≫ evaluationBase p U.val =
      p.fiberToSpecResidueField s ≫ FrameBundle.residueBaseLift U s hs := by
  apply (cancel_mono U.val.ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, fibreSourceLift_ι,
    Category.assoc, FrameBundle.residueBaseLift_ι, p.fiber_fac]

/-- The genuine local evaluation sections pulled back to the actual source fibre. -/
def fibreEvaluationSections (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    Fin (n + 1) → GlobalSections
      ((LineBundle.pullback (fibreSourceLift p U s hs)).obj
        (evaluationLineBundle p L U.val)).obj :=
  fun i => pullbackSection (fibreSourceLift p U s hs)
    (evaluationLineBundle p L U.val).obj
    (localEvaluationSections p L ev (frame M n U) U.val le_rfl i)

include hgen in
/-- Pullback preserves generation of these particular actual sections. -/
lemma fibreEvaluationSections_generate (U : FrameOpen M n) (s : S)
    (hs : s ∈ U.val) :
    ∀ x : p.fiber s, ∃ i, x ∈ nonvanishingLocus
      ((LineBundle.pullback (fibreSourceLift p U s hs)).obj
        (evaluationLineBundle p L U.val)).obj
      (fibreEvaluationSections p L ev U s hs i) :=
  pullbackSections_generate (fibreSourceLift p U s hs) (hgen U)

/-- Evaluation in a nearby frame, now valued in projective space over the
original residue field. -/
def fibreEvaluationCoordinates (U : FrameOpen M n) (s : S) (hs : s ∈ U.val) :
    p.fiber s ⟶ RelativeProjectiveSpace (Spec (S.residueField s)) n :=
  relativeLinearSystemMap (p.fiberToSpecResidueField s)
    (fibreEvaluationSections_generate p L ev hgen U s hs)

@[reassoc (attr := simp)]
lemma fibreEvaluationCoordinates_toBase (U : FrameOpen M n) (s : S)
    (hs : s ∈ U.val) :
    fibreEvaluationCoordinates p L ev hgen U s hs ≫
        RelativeProjectiveSpace.toBase (Spec (S.residueField s)) n =
      p.fiberToSpecResidueField s :=
  relativeLinearSystemMap_toBase _ _

/-- The explicit fibre coordinates are precisely the restriction of global
evaluation, expressed through the actual projective-fibre chart. -/
@[reassoc (attr := simp)]
lemma fibreEvaluationCoordinates_toBundle (U : FrameOpen M n) (s : S)
    (hs : s ∈ U.val) :
    fibreEvaluationCoordinates p L ev hgen U s hs ≫
        FrameBundle.fibreChartMap hM U s hs =
      p.fiberι s ≫ evaluationMap p L ev hM hgen := by
  have h := evaluationMap_chartBaseChange p L ev hM hgen U
    (FrameBundle.residueBaseLift U s hs) (p.fiberToSpecResidueField s)
    (fibreSourceLift p U s hs) (fibreSourceLift_toBase p U s hs)
  simpa only [fibreEvaluationCoordinates, fibreEvaluationSections_generate,
    fibreEvaluationSections, FrameBundle.fibreChartMap, fibreSourceLift_ι_assoc] using h

/-- The coordinates identify the canonical whole-fibre evaluation map, rather
than only its composite into the global bundle. -/
lemma fibreEvaluationCoordinates_fibreChartIso (U : FrameOpen M n) (s : S)
    (hs : s ∈ U.val) :
    fibreEvaluationCoordinates p L ev hgen U s hs ≫
        (FrameBundle.fibreChartIso hM U s hs).hom =
      pullback.map p (S.fromSpecResidueField s) (FrameBundle.toBase hM)
        (S.fromSpecResidueField s) (evaluationMap p L ev hM hgen)
        (𝟙 _) (𝟙 _) (by simp) (by simp) := by
  apply pullback.hom_ext
  · change _ ≫ (FrameBundle.toBase hM).fiberι s = _
    rw [Category.assoc, FrameBundle.fibreChartIso_hom_fiberι,
      fibreEvaluationCoordinates_toBundle]
    simp [Scheme.Hom.fiberι]
  · change _ ≫ (FrameBundle.toBase hM).fiberToSpecResidueField s = _
    rw [Category.assoc, FrameBundle.fibreChartIso_hom_toResidueField,
      fibreEvaluationCoordinates_toBase]
    simp [Scheme.Hom.fiberToSpecResidueField]

end Langlands.AlgebraicGeometry.ProjectiveBundle

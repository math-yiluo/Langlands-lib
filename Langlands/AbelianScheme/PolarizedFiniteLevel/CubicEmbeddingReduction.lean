import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreSections
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicDirectImageProof

/-! # The relative cubic embedding from its field case -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.ProjectiveBundle
open Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- The field Lefschetz statement gives relative generation of the full cubic
evaluation over every locally noetherian base. -/
theorem Datum.cubicEvaluationGenerates_of_fieldEmbedding
    (HF : CubicFieldEmbeddingStatement.{u}) [IsLocallyNoetherian S] (hd : 0 < d)
    (a : Datum P S g d n) :
    EvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule) :=
  Datum.cubicEvaluationGenerates_of_directImage cubicDirectImage hd a fun s =>
    (HF P (S.residueField s) g d n hd (a.pullback (S.fromSpecResidueField s))).1

/-- The field Lefschetz statement makes the actual full cubic projective
evaluation a closed immersion over every locally noetherian base. -/
theorem Datum.isClosedImmersion_cubicProjectiveEvaluation_of_fieldEmbedding
    (HF : CubicFieldEmbeddingStatement.{u}) [IsLocallyNoetherian S] (hd : 0 < d)
    (a : Datum P S g d n)
    (hM : IsLocallyFreeOfRank a.rigidificationModule (6 ^ g * d))
    (hgen : EvaluationGenerates a.abelian.X.hom a.cubicBundle
      (𝟙 a.rigidificationModule)) :
    IsClosedImmersion (a.cubicProjectiveEvaluation hd hM hgen) := by
  have := hM.isLocallyFree
  have : a.rigidificationModule.IsQuasicoherent := inferInstance
  rw [a.isClosedImmersion_cubicProjectiveEvaluation_iff_fibre hd hM hgen]
  intro s
  obtain ⟨U, hs, hU⟩ := exists_affine_frameOpen (a.cubicProjectiveRank hd hM) s
  have : IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField s)) :=
    (cubicDirectImage P S g d n hd a).2 _ (S.fromSpecResidueField s)
  -- the second clause of `HF` for the actual full cubic basis of the residue datum
  have hci : IsClosedImmersion
      (relativeLinearSystemMap (a.abelian.X.hom.fiberToSpecResidueField s)
        (a.cubicFibreSectionBasis_generate hgen U hU s hs)) :=
    (HF P (S.residueField s) g d n hd (a.pullback (S.fromSpecResidueField s))).2 _
      (a.cubicFibreSectionBasis U hU s hs) (a.cubicFibreSectionBasis_generate hgen U hU s hs)
  rw [a.cubicFibreSectionBasis_coordinates hgen U hU s hs] at hci
  have hfin : IsClosedImmersion
      (fibreEvaluationCoordinates a.abelian.X.hom a.cubicBundle
          (𝟙 a.rigidificationModule) (hgen.frameEvaluationGenerates _ _ _) U s hs ≫
        (FrameBundle.fibreChartIso (a.cubicProjectiveRank hd hM) U s hs).hom) :=
    inferInstance
  rw [fibreEvaluationCoordinates_fibreChartIso] at hfin
  exact hfin

set_option linter.defProp false in
/-- Proved definition: from the field Lefschetz statement, the actual cubic
direct image of every datum over a locally noetherian base has rank `6^g*d`,
its full evaluation generates, and the resulting projective evaluation is a
closed immersion. -/
def Datum.cubicProjectiveEmbedding_of_fieldEmbedding
    (HF : CubicFieldEmbeddingStatement.{u}) [IsLocallyNoetherian S] (hd : 0 < d)
    (a : Datum P S g d n) :
    ∃ (hM : IsLocallyFreeOfRank a.rigidificationModule (6 ^ g * d))
      (hgen : EvaluationGenerates a.abelian.X.hom a.cubicBundle
        (𝟙 a.rigidificationModule)),
      IsClosedImmersion (a.cubicProjectiveEvaluation hd hM hgen) :=
  ⟨(cubicDirectImage P S g d n hd a).1, a.cubicEvaluationGenerates_of_fieldEmbedding HF hd,
    a.isClosedImmersion_cubicProjectiveEvaluation_of_fieldEmbedding HF hd _ _⟩

end Langlands.AbelianScheme.PolarizedFiniteLevel

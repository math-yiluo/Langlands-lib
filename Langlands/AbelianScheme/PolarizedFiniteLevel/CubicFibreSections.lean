import Langlands.AlgebraicGeometry.ProjectiveBundle.EvaluationFibreFullSections
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveFibres
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicSectionRigidity
import Langlands.AlgebraicGeometry.LinearSystem.CoefficientComparison

/-! # Actual full cubic sections on the original residue fibres -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.ProjectiveBundle
open Langlands.AlgebraicGeometry.LinearSystem
open Langlands.AlgebraicGeometry.Modules.DerivedSections

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S S' : Scheme.{u}} {g d n m : ℕ}
    (a : Datum P S g d n)

/-- The retained canonical cubic direct-image isomorphism also makes the
comparison to the single pulled-back cubic bundle invertible. -/
lemma Datum.isIso_cubicBaseChangeEvaluation (b : S' ⟶ S)
    [IsIso (a.rigidificationBaseChangeMap b)] :
    IsIso (baseChangeEvaluation a.abelian.X.hom a.cubicBundle
      (𝟙 a.rigidificationModule) b (a.pullback b).abelian.X.hom
      (pullback.fst a.abelian.X.hom b) pullback.condition) := by
  let e := (LineBundle.forget _).mapIso (a.cubicBundlePullbackIso b)
  have he :
      baseChangeEvaluation a.abelian.X.hom a.cubicBundle
          (𝟙 a.rigidificationModule) b (a.pullback b).abelian.X.hom
          (pullback.fst a.abelian.X.hom b) pullback.condition ≫
        (Scheme.Modules.pushforward (a.pullback b).abelian.X.hom).map e.inv =
      a.rigidificationBaseChangeMap b := by
    simp [baseChangeEvaluation, Datum.rigidificationBaseChangeMap, e]
  have : IsIso
      (baseChangeEvaluation a.abelian.X.hom a.cubicBundle
          (𝟙 a.rigidificationModule) b (a.pullback b).abelian.X.hom
          (pullback.fst a.abelian.X.hom b) pullback.condition ≫
        (Scheme.Modules.pushforward (a.pullback b).abelian.X.hom).map e.inv) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right
    _ ((Scheme.Modules.pushforward (a.pullback b).abelian.X.hom).map e.inv)

variable [a.rigidificationModule.IsQuasicoherent]

/-- A full section basis for the actual cubic bundle of the actual
residue-field datum, with the canonical comparison hypothesis retained. -/
def Datum.cubicFibreSectionBasis (U : FrameOpen a.rigidificationModule m)
    (hU : IsAffineOpen U.val) (s : S) (hs : s ∈ U.val)
    [IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField s))] :
    Module.Basis (Fin (m + 1)) (S.residueField s)
      ((relativeGlobalSections (a.pullback (S.fromSpecResidueField s)).abelian.X.hom).obj
        (a.pullback (S.fromSpecResidueField s)).cubicBundle.obj) := by
  letI : IsIso (baseChangeEvaluation a.abelian.X.hom a.cubicBundle
      (𝟙 a.rigidificationModule) (S.fromSpecResidueField s)
      (a.abelian.X.hom.fiberToSpecResidueField s) (a.abelian.X.hom.fiberι s)
      (a.abelian.X.hom.fiber_fac s)) :=
    a.isIso_cubicBaseChangeEvaluation (S.fromSpecResidueField s)
  exact (fibreFullSectionBasis a.abelian.X.hom a.cubicBundle
      (𝟙 a.rigidificationModule) U hU s hs).map
    ((relativeGlobalSections (a.abelian.X.hom.fiberToSpecResidueField s)).mapIso
      (((LineBundle.forget _).mapIso
        (a.cubicBundlePullbackIso (S.fromSpecResidueField s))).symm)).toLinearEquiv

/-- Each full cubic basis entry is the canonical changed evaluation section
transported through the specified cubic-bundle comparison. -/
@[simp]
lemma Datum.cubicFibreSectionBasis_apply (U : FrameOpen a.rigidificationModule m)
    (hU : IsAffineOpen U.val) (s : S) (hs : s ∈ U.val)
    [IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField s))]
    (i : Fin (m + 1)) :
    a.cubicFibreSectionBasis U hU s hs i =
      (((LineBundle.forget _).mapIso
        (a.cubicBundlePullbackIso (S.fromSpecResidueField s))).inv.app ⊤)
          (fibreFrameEvaluation a.abelian.X.hom a.cubicBundle
            (𝟙 a.rigidificationModule) U s hs i) := by
  let : IsIso (baseChangeEvaluation a.abelian.X.hom a.cubicBundle
      (𝟙 a.rigidificationModule) (S.fromSpecResidueField s)
      (a.abelian.X.hom.fiberToSpecResidueField s) (a.abelian.X.hom.fiberι s)
      (a.abelian.X.hom.fiber_fac s)) :=
    a.isIso_cubicBaseChangeEvaluation (S.fromSpecResidueField s)
  unfold Datum.cubicFibreSectionBasis
  erw [Module.Basis.map_apply, fibreFullSectionBasis_apply]
  rfl

variable
    (hgen : EvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule))

include hgen in
/-- The transported full basis generates under the retained original
evaluation-generation hypothesis. -/
lemma Datum.cubicFibreSectionBasis_generate (U : FrameOpen a.rigidificationModule m)
    (hU : IsAffineOpen U.val) (s : S) (hs : s ∈ U.val)
    [IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField s))] :
    ∀ x : (a.pullback (S.fromSpecResidueField s)).abelian.X.left, ∃ i,
      x ∈ nonvanishingLocus (a.pullback (S.fromSpecResidueField s)).cubicBundle.obj
        (a.cubicFibreSectionBasis U hU s hs i) := by
  have ht := mapIsoSections_generate
    (L := (LineBundle.pullback (a.abelian.X.hom.fiberι s)).obj a.cubicBundle)
    (M := (a.pullback (S.fromSpecResidueField s)).cubicBundle)
    (((LineBundle.forget _).mapIso
      (a.cubicBundlePullbackIso (S.fromSpecResidueField s))).symm)
    (fibreFrameEvaluation_generate a.abelian.X.hom a.cubicBundle
      (𝟙 a.rigidificationModule)
      (hgen.frameEvaluationGenerates _ _ _) U s hs)
  intro x
  obtain ⟨i, hi⟩ := ht x
  refine ⟨i, ?_⟩
  rw [Datum.cubicFibreSectionBasis_apply]
  exact hi

/-- The actual full cubic basis has precisely the previously constructed
relative coordinates of the whole-fibre projective evaluation. -/
lemma Datum.cubicFibreSectionBasis_coordinates (U : FrameOpen a.rigidificationModule m)
    (hU : IsAffineOpen U.val) (s : S) (hs : s ∈ U.val)
    [IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField s))] :
    relativeLinearSystemMap (a.abelian.X.hom.fiberToSpecResidueField s)
        (a.cubicFibreSectionBasis_generate hgen U hU s hs) =
      fibreEvaluationCoordinates a.abelian.X.hom a.cubicBundle
        (𝟙 a.rigidificationModule)
        (hgen.frameEvaluationGenerates _ _ _) U s hs := by
  have ht := relativeLinearSystemMap_mapIso (a.abelian.X.hom.fiberToSpecResidueField s)
    (L := (LineBundle.pullback (a.abelian.X.hom.fiberι s)).obj a.cubicBundle)
    (M := (a.pullback (S.fromSpecResidueField s)).cubicBundle)
    (((LineBundle.forget _).mapIso
      (a.cubicBundlePullbackIso (S.fromSpecResidueField s))).symm)
    (fibreFrameEvaluation_generate a.abelian.X.hom a.cubicBundle
      (𝟙 a.rigidificationModule)
      (hgen.frameEvaluationGenerates _ _ _) U s hs)
  have he : mapIsoSections
      (L := (LineBundle.pullback (a.abelian.X.hom.fiberι s)).obj a.cubicBundle)
      (M := (a.pullback (S.fromSpecResidueField s)).cubicBundle)
      (((LineBundle.forget _).mapIso
        (a.cubicBundlePullbackIso (S.fromSpecResidueField s))).symm)
      (fibreFrameEvaluation a.abelian.X.hom a.cubicBundle
        (𝟙 a.rigidificationModule) U s hs) =
      (fun i => a.cubicFibreSectionBasis U hU s hs i) := by
    funext i
    exact (a.cubicFibreSectionBasis_apply U hU s hs i).symm
  simpa only [he] using ht.trans
    (fibreFrameEvaluation_coordinates a.abelian.X.hom a.cubicBundle
      (𝟙 a.rigidificationModule)
      (hgen.frameEvaluationGenerates _ _ _) U s hs)

/-- The polynomial section map of the full cubic basis gives the same
relative coordinates over the original residue field. -/
lemma Datum.cubicFibreSectionBasis_toRelative (U : FrameOpen a.rigidificationModule m)
    (hU : IsAffineOpen U.val) (s : S) (hs : s ∈ U.val)
    [IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField s))] :
    (a.pullback (S.fromSpecResidueField s)).cubicSectionMap
        (a.cubicFibreSectionBasis U hU s hs)
        (a.cubicFibreSectionBasis_generate hgen U hU s hs) ≫
      (Langlands.AlgebraicGeometry.RelativeProjectiveSpace.affineComparisonIso
        (S.residueField s) m).hom =
      fibreEvaluationCoordinates a.abelian.X.hom a.cubicBundle
        (𝟙 a.rigidificationModule)
        (hgen.frameEvaluationGenerates _ _ _) U s hs := by
  apply (cancel_mono
    (Langlands.AlgebraicGeometry.RelativeProjectiveSpace.affineComparisonIso
      (S.residueField s) m).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← a.cubicFibreSectionBasis_coordinates hgen U hU s hs]
  symm
  have hp : (a.pullback (S.fromSpecResidueField s)).abelian.X.hom =
      a.abelian.X.hom.fiberToSpecResidueField s := rfl
  simpa only [Langlands.AlgebraicGeometry.RelativeProjectiveSpace.toPolynomial,
    Langlands.AlgebraicGeometry.RelativeProjectiveSpace.map_id, Category.id_comp,
    Category.comp_id, Datum.cubicSectionMap, hp] using
    relativeLinearSystemMap_toPolynomial
      (K := S.residueField s)
      (a.abelian.X.hom.fiberToSpecResidueField s) (𝟙 _)
      (a.cubicFibreSectionBasis_generate hgen U hU s hs)

variable (hd : 0 < d)
    (hM : IsLocallyFreeOfRank a.rigidificationModule (6 ^ g * d))

/-- The polynomial projective model of the cubic projective-bundle fibre
in a chosen frame, over the original residue field. -/
def Datum.cubicProjectiveFibreChartIso
    (U : FrameOpen a.rigidificationModule (cubicProjectiveDimension g d))
    (s : S) (hs : s ∈ U.val) :
    Langlands.AlgebraicGeometry.ProjectiveSpace (S.residueField s)
        (cubicProjectiveDimension g d) ≅
      (a.cubicProjectiveProjection hd hM).fiber s :=
  Langlands.AlgebraicGeometry.RelativeProjectiveSpace.affineComparisonIso
      (S.residueField s) (cubicProjectiveDimension g d) ≪≫
    FrameBundle.fibreChartIso (a.cubicProjectiveRank hd hM) U s hs

/-- The actual full cubic section map is precisely the whole-fibre
evaluation map in the specified polynomial projective chart. -/
lemma Datum.cubicFibreSectionBasis_toEvaluationFibre
    (U : FrameOpen a.rigidificationModule (cubicProjectiveDimension g d))
    (hU : IsAffineOpen U.val) (s : S) (hs : s ∈ U.val)
    [IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField s))] :
    (a.pullback (S.fromSpecResidueField s)).cubicSectionMap
        (a.cubicFibreSectionBasis U hU s hs)
        (a.cubicFibreSectionBasis_generate hgen U hU s hs) ≫
      (a.cubicProjectiveFibreChartIso hd hM U s hs).hom =
      a.cubicProjectiveEvaluationFibre hd hM hgen s := by
  change _ ≫
    ((Langlands.AlgebraicGeometry.RelativeProjectiveSpace.affineComparisonIso
      (S.residueField s) (cubicProjectiveDimension g d)).hom ≫
      (FrameBundle.fibreChartIso (a.cubicProjectiveRank hd hM) U s hs).hom) = _
  rw [← Category.assoc, a.cubicFibreSectionBasis_toRelative hgen U hU s hs]
  exact fibreEvaluationCoordinates_fibreChartIso a.abelian.X.hom a.cubicBundle
    (𝟙 a.rigidificationModule) (a.cubicProjectiveRank hd hM)
    (hgen.frameEvaluationGenerates _ _ _) U s hs

/-- Closed immersion of the full cubic section map is equivalent to closed
immersion of the actual whole-fibre evaluation. -/
lemma Datum.isClosedImmersion_cubicFibreSectionBasis_iff
    (U : FrameOpen a.rigidificationModule (cubicProjectiveDimension g d))
    (hU : IsAffineOpen U.val) (s : S) (hs : s ∈ U.val)
    [IsIso (a.rigidificationBaseChangeMap (S.fromSpecResidueField s))] :
    IsClosedImmersion
        ((a.pullback (S.fromSpecResidueField s)).cubicSectionMap
          (a.cubicFibreSectionBasis U hU s hs)
          (a.cubicFibreSectionBasis_generate hgen U hU s hs)) ↔
      IsClosedImmersion (a.cubicProjectiveEvaluationFibre hd hM hgen s) := by
  rw [← a.cubicFibreSectionBasis_toEvaluationFibre hgen hd hM U hU s hs]
  exact (MorphismProperty.cancel_right_of_respectsIso
    @IsClosedImmersion _ (a.cubicProjectiveFibreChartIso hd hM U s hs).hom).symm

end Langlands.AbelianScheme.PolarizedFiniteLevel

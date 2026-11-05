import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicProjectiveEvaluation
import Langlands.AlgebraicGeometry.RelativeFibreClosedImmersion
import Langlands.AlgebraicGeometry.Picard.LineBundleIsoLemmas

/-! # Actual residue fibres of cubic projective evaluation -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.ProjectiveBundle

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}
    (a : Datum P S g d n) (hd : 0 < d)
    (hM : IsLocallyFreeOfRank a.rigidificationModule (6 ^ g * d))
    (hgen : EvaluationGenerates a.abelian.X.hom a.cubicBundle (𝟙 a.rigidificationModule))

/-- Cubic evaluation on the actual fibre of the original abelian structure map. -/
def Datum.cubicProjectiveEvaluationFibre (s : S) :
    a.abelian.X.hom.fiber s ⟶ (a.cubicProjectiveProjection hd hM).fiber s :=
  pullback.map _ _ _ _ (a.cubicProjectiveEvaluation hd hM hgen) (𝟙 _) (𝟙 _)
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma Datum.cubicProjectiveEvaluationFibre_fiberι (s : S) :
    a.cubicProjectiveEvaluationFibre hd hM hgen s ≫
        (a.cubicProjectiveProjection hd hM).fiberι s =
      a.abelian.X.hom.fiberι s ≫ a.cubicProjectiveEvaluation hd hM hgen := by
  simp [Datum.cubicProjectiveEvaluationFibre, Scheme.Hom.fiberι]

@[reassoc (attr := simp)]
lemma Datum.cubicProjectiveEvaluationFibre_toResidueField (s : S) :
    a.cubicProjectiveEvaluationFibre hd hM hgen s ≫
        (a.cubicProjectiveProjection hd hM).fiberToSpecResidueField s =
      a.abelian.X.hom.fiberToSpecResidueField s := by
  simp [Datum.cubicProjectiveEvaluationFibre, Scheme.Hom.fiberToSpecResidueField]

/-- The actual fibre evaluation as a morphism over the actual residue field. -/
def Datum.cubicProjectiveEvaluationFibreOver (s : S) :
    Over.mk (a.abelian.X.hom.fiberToSpecResidueField s) ⟶
      Over.mk ((a.cubicProjectiveProjection hd hM).fiberToSpecResidueField s) :=
  Over.homMk (a.cubicProjectiveEvaluationFibre hd hM hgen s)
    (a.cubicProjectiveEvaluationFibre_toResidueField hd hM hgen s)

/-- The constructed fibre evaluation is the Cartesian restriction of evaluation. -/
lemma Datum.isPullback_cubicProjectiveEvaluationFibre (s : S) :
    IsPullback (a.abelian.X.hom.fiberι s)
      (a.cubicProjectiveEvaluationFibre hd hM hgen s)
      (a.cubicProjectiveEvaluation hd hM hgen)
      ((a.cubicProjectiveProjection hd hM).fiberι s) := by
  have ho : IsPullback
      (a.cubicProjectiveEvaluationFibre hd hM hgen s ≫
        (a.cubicProjectiveProjection hd hM).fiberToSpecResidueField s)
      (a.abelian.X.hom.fiberι s) (S.fromSpecResidueField s)
      (a.cubicProjectiveEvaluation hd hM hgen ≫ a.cubicProjectiveProjection hd hM) := by
    rw [a.cubicProjectiveEvaluation_toBase hd hM hgen,
      a.cubicProjectiveEvaluationFibre_toResidueField hd hM hgen s]
    exact (IsPullback.of_hasPullback a.abelian.X.hom (S.fromSpecResidueField s)).flip
  exact (ho.of_right (a.cubicProjectiveEvaluationFibre_fiberι hd hM hgen s)
    (IsPullback.of_hasPullback (a.cubicProjectiveProjection hd hM)
      (S.fromSpecResidueField s)).flip).flip

instance Datum.isProper_cubicProjectiveEvaluationFibre (s : S) :
    IsProper (a.cubicProjectiveEvaluationFibre hd hM hgen s) :=
  MorphismProperty.of_isPullback (a.isPullback_cubicProjectiveEvaluationFibre hd hM hgen s)
    (inferInstance : IsProper (a.cubicProjectiveEvaluation hd hM hgen))

/-- Degree one on the target fibre pulls back to the actual cubic bundle of
the actual pulled-back datum. -/
def Datum.cubicProjectiveEvaluationFibrePullbackIso (s : S) :
    (LineBundle.pullback (a.cubicProjectiveEvaluationFibre hd hM hgen s)).obj
        ((LineBundle.pullback ((a.cubicProjectiveProjection hd hM).fiberι s)).obj
          (a.cubicProjectiveTwistOne hd hM)) ≅
      (a.pullback (S.fromSpecResidueField s)).cubicBundle :=
  LineBundle.pullbackCompEqIso _ _
      (a.cubicProjectiveEvaluationFibre_fiberι hd hM hgen s) _ ≪≫
    ((LineBundle.pullbackComp (a.abelian.X.hom.fiberι s)
      (a.cubicProjectiveEvaluation hd hM hgen)).app _).symm ≪≫
    (LineBundle.pullback (a.abelian.X.hom.fiberι s)).mapIso
      (a.cubicProjectiveEvaluationPullbackIso hd hM hgen) ≪≫
    (a.cubicBundlePullbackIso (S.fromSpecResidueField s)).symm

/-- Closed immersion of actual cubic evaluation is detected on its actual
original-base residue fibres. -/
lemma Datum.isClosedImmersion_cubicProjectiveEvaluation_iff_fibre :
    IsClosedImmersion (a.cubicProjectiveEvaluation hd hM hgen) ↔
      ∀ s : S, IsClosedImmersion (a.cubicProjectiveEvaluationFibre hd hM hgen s) := by
  constructor
  · intro h s
    exact MorphismProperty.of_isPullback
      (a.isPullback_cubicProjectiveEvaluationFibre hd hM hgen s) h
  intro H
  apply (Langlands.AlgebraicGeometry.isClosedImmersion_iff_fibre_of_isProper
    (a.cubicProjectiveEvaluation hd hM hgen)).mpr
  intro y
  let q := a.cubicProjectiveProjection hd hM
  have hrel : IsClosedImmersion
      ((a.cubicProjectiveEvaluationFibre hd hM hgen (q y)).fiberToSpecResidueField
        (q.asFiber y)) :=
    MorphismProperty.pullback_snd _ _ (H (q y))
  have h := (Langlands.AlgebraicGeometry.fibreClosedImmersion_iff_of_isPullback_of_residueIso
    (a.isPullback_cubicProjectiveEvaluationFibre hd hM hgen (q y)) (q.asFiber y)).mp hrel
  exact Eq.mp (congrArg
    (fun z ↦ IsClosedImmersion ((a.cubicProjectiveEvaluation hd hM hgen).fiberToSpecResidueField z))
    (q.fiberι_asFiber y)) h

end Langlands.AbelianScheme.PolarizedFiniteLevel

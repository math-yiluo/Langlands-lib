import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof
import Langlands.AllField.Group.GL.CountabilityProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement
/-!
# Continued unequal-rank bilinear forms at block zero

Proof of `UnequalRankBlockZeroContinuedFormsStatement`. The two forms are the
evaluations at `q^{-s}` and `q^{-(1-s)}` of the bilinear families of rational
continuations of the original `(0,k)` integral and of the inverse-transpose
`(k,0)` integral of the dual model vectors. The finite exceptional set consists
of the roots of the original normalized generator and the reflections
`w ↦ (q w)⁻¹` of the roots of the dual normalized generator.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankBlockZeroContinuedFormsStatement UnequalRankCommonGeneratorStatement UnequalRankFunctionalEquationStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow padic_quotient_sigmaFinite padic_rectangular_laws padic_row_instances unequalRankBlockZeroContinuedForms
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.RationalEvaluation
open scoped NNReal

universe uF uV uW

section RectangularIntegrals

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {k t : ℕ} [BorelSpace (Matrix (Fin k) (Fin t) F)]

end RectangularIntegrals

section Spectral

end Spectral

section Assembly

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

end Assembly

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The right-scaling and affine-invariance laws of the rectangular product
measure built from any additive Haar measure, for the normalized absolute value. -/
theorem padic_rectangular_laws (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ ν : AdditiveHaarMeasure F,
      (∀ (g : Langlands.GeneralLinear (n + 1) F)
        (G : Matrix (Fin k) (Fin (n + 1)) F → ℂ),
        ∫ x, G (x * g.val) ∂(rectangularMeasure ν k (n + 1)) =
          determinantWeight (normalizedAbsoluteValue T) g (-((k : ℕ) : ℂ)) *
            ∫ x, G x ∂(rectangularMeasure ν k (n + 1))) ∧
      (∀ A : Matrix (Fin k) (Fin k) F, A.det = 1 →
        ∀ (c : Matrix (Fin k) (Fin (n + 1)) F)
          (G : Matrix (Fin k) (Fin (n + 1)) F → ℂ),
          ∫ x, G (A * x + c) ∂(rectangularMeasure ν k (n + 1)) =
            ∫ x, G x ∂(rectangularMeasure ν k (n + 1))) := by
  intro ν
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : SecondCountableTopology F := T.secondCountableTopology
  have : SigmaCompactSpace F := T.sigmaCompactSpace
  refine ⟨fun g G => ?_, fun A hA c G => ?_⟩
  · have h := padicRectangularHaarScaling F T k (n + 1) (rectangularMeasure ν k (n + 1)) 1 g⁻¹
    have he : (fun X : Matrix (Fin k) (Fin (n + 1)) F =>
        ((1 : Langlands.GeneralLinear k F) : Matrix (Fin k) (Fin k) F) * X *
          ((g⁻¹⁻¹ : Langlands.GeneralLinear (n + 1) F) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
        ⇑(matrixMulRightEquiv (k := k) g) := by
      funext X
      simp [matrixMulRightEquiv]
    rw [he] at h
    rw [show (fun x => G (x * g.val)) = fun x => G (matrixMulRightEquiv (k := k) g x) from rfl,
      integral_comp_of_map_eq_smul _ h]
    congr 1
    simp only [map_one, map_inv, Units.val_one, one_pow, Units.val_inv_eq_inv_val, one_div,
      inv_inv, NNReal.coe_pow, NNReal.coe_inv, Langlands.LocalFieldData.determinantNorm_coe,
      determinantWeight, normalizedAbsoluteValue_apply, Matrix.GeneralLinearGroup.val_det_apply,
      Complex.cpow_neg, Complex.cpow_natCast]
    push_cast
    rw [inv_pow]
  · let A' : Langlands.GeneralLinear k F :=
      Matrix.nonsingInvUnit A (by rw [hA]; exact isUnit_one)
    have hA' : GeneralLinear.determinant A' = 1 := Units.ext hA
    have h := padicRectangularHaarScaling F T k (n + 1) (rectangularMeasure ν k (n + 1)) A' 1
    have he : (fun X : Matrix (Fin k) (Fin (n + 1)) F =>
        (A' : Matrix (Fin k) (Fin k) F) * X *
          ((1⁻¹ : Langlands.GeneralLinear (n + 1) F) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
        ⇑(matrixMulLeftEquiv (t := n + 1) A') := by
      funext X
      simp [matrixMulLeftEquiv]
    have hdet : T.determinantNorm k A' = 1 := by
      change T.normalizedAbsUnits (GeneralLinear.determinant A') = 1
      rw [hA', map_one]
    rw [he, hdet, map_one] at h
    simp only [Units.val_one, one_pow, div_one, inv_one, one_smul] at h
    exact integral_affine_eq_self A' h c G

/-- The supplied compatible quotient measure is sigma finite. -/
theorem padic_quotient_sigmaFinite (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n F)
    ∀ μ : Measure (LeftUnipotentQuotient n F), μ.Regular → SigmaFinite μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n F)
  intro μ hμ
  have : SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
    T.generalLinearSigmaCompactSpace (n + 1)
  have : SigmaCompactSpace (LeftUnipotentQuotient n F) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr (Quotient.mk_surjective (s := QuotientGroup.rightRel
      (upperUnipotent (n + 1) F)))]
    exact isSigmaCompact_range continuous_quot_mk
  infer_instance

end Padic

/-- **Continued unequal-rank bilinear forms at block zero.** Proof of
`UnequalRankBlockZeroContinuedFormsStatement`. -/
theorem unequalRankBlockZeroContinuedForms (F : Type uF) [Field F]
    (T : LocalFieldData F) (n r : ℕ) :
    UnequalRankBlockZeroContinuedFormsStatement.{uF, uV, uW} F T n r := by
  have hrect := padic_rectangular_laws T n (r - n - 1)
  have hinst := padic_row_instances T n
  have hquot := padic_quotient_sigmaFinite T n
  unfold UnequalRankBlockZeroContinuedFormsStatement
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro hnr ψ _ μ hμ ν V _ _ W _ _ π σ _ _ ℓ ℓ' _ _ k hr q abv hA hAd
  obtain ⟨-, hS⟩ := hinst ν
  have : SigmaFinite μ := hquot μ hμ.regular
  exact blockZeroContinuedForms_of_laws hnr T.residueCardinality_gt_one ψ abv μ
    hμ.right_invariant ν π σ ℓ ℓ' (fun g => ⟨_, normalizedAbsoluteValue_det_eq_zpow T g⟩)
    (hrect ν).1 (hrect ν).2 hA hAd

end Langlands.AllField.RankinSelberg

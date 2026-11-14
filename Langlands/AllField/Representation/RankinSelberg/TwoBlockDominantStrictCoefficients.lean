import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictCoefficients
import Langlands.AllField.Representation.RankinSelberg.EqualRankSliceSupportProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankDeterminantSlices
/-!
# Actual strictly dominant coefficient support

The support argument uses only the smooth larger Whittaker coefficient.
Convergence and the two first-block Laurent identities remain separate.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding strictCoefficientBorel strictCoefficientMeasurable strictCoefficientQuotientMeasurable strictCoefficientSecondCountable strictCoefficientTopology strictRectangleMeasure strictSliceCoefficient strictSliceCoefficient_lowerSupport unequalRankSliceCoefficient_lowerSupport
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_schwartzBruhat_row_bound hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance strictCoefficientSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance strictCoefficientMeasurable : MeasurableSpace F := borel _
local instance strictCoefficientBorel : BorelSpace F := ⟨rfl⟩
local instance strictCoefficientQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _

variable {n r j k : ℕ}

/-- The supplied scalar Haar's rectangle product, with only its measurable
space identified with the canonical Borel space. -/
def strictRectangleMeasure (ν : AdditiveHaarMeasure F) (a b : ℕ) :
    @Measure (Matrix (Fin a) (Fin b) F) (borel _) :=
  (show (inferInstance : MeasurableSpace (Matrix (Fin a) (Fin b) F)) =
      borel _ from
    @BorelSpace.measurable_eq _ _ _
      (inferInstanceAs (BorelSpace (Fin a → Fin b → F)))) ▸
    rectangularMeasure ν a b

/-- Fixed larger rank wrapper for the actual unequal-rank slice coefficient. -/
def strictSliceCoefficient (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    (Wtest : WhittakerFunctions ψ r) (Wjac : InverseWhittakerFunctions ψ n) :
    BilateralLaurentSeries :=
  unequalRankSliceCoefficient F j k ψ μ
    (strictRectangleMeasure F ν j (n + 1)) (hr ▸ Wtest) Wjac

/-- The unequal-rank coefficients have a finite negative tail. No assumption
on the smaller Whittaker function or either supplied measure is needed. -/
theorem unequalRankSliceCoefficient_lowerSupport
    (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : @Measure (Matrix (Fin j) (Fin (n + 1)) F) (borel _))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + (j + k + 1) + 1) F) V)
    (hπ : IsSmooth π)
    (lambda : glFunctionals ψ (n + (j + k + 1)) π)
    (f : (coefficientModel π lambda).toSubmodule)
    (Wjac : InverseWhittakerFunctions ψ n) :
    HasLowerBoundedSupport
      (unequalRankSliceCoefficient F j k ψ μ ν f.val Wjac) := by
  obtain ⟨R, hR, hroot⟩ := Langlands.AllField.Whittaker.smoothSimpleRootSupport F
    (⟨⟩ : LocalFieldData F) (n + (j + k + 1)) ψ V π hπ lambda f
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt
    (∏ i : Fin (n + (j + k + 1) + 1), R ^ (n + (j + k + 1) - i.val) * 1) hq
  refine (hasLowerBoundedSupport_iff _).2 ⟨-(N : ℤ), fun d hd => ?_⟩
  unfold unequalRankSliceCoefficient sliceCoefficient
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro q hqd
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hqd
    unfold unequalRankAverage
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro x
    have hzero : f.val.val (unequalRankMatrix j k g x) = 0 := by
      by_contra hnonzero
      have hrow (b : Fin (n + (j + k + 1) + 1)) :
          (⟨⟩ : LocalFieldData F).normalizedAbs
            (lastRow (unequalRankMatrix j k g x) b) ≤ 1 := by
        rw [lastRow, unequalRankMatrix_val]
        simp [appendIdentity_entry, rectangularEntries, Fin.val_last,
          show ¬n + (j + k + 1) < n + 1 by omega,
          show ¬n + (j + k + 1) < n + 1 + j by omega]
        split_ifs <;> simp [(⟨⟩ : LocalFieldData F).normalizedAbs_one,
          (⟨⟩ : LocalFieldData F).normalizedAbs_zero]
      have hdet := normalizedAbs_determinant_le_of_simpleRoot
        (⟨⟩ : LocalFieldData F) (n + (j + k + 1)) ψ f.val hR zero_le_one
        hroot (unequalRankMatrix j k g x) hnonzero hrow
      rw [determinant_unequalRankMatrix,
        (⟨⟩ : LocalFieldData F).normalizedAbs_of_ne_zero
          (GeneralLinear.determinant g).ne_zero, hqd] at hdet
      have hle :
          ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (N : ℤ) ≤
            ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (-d) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_natCast] at hle
      linarith
    simp [unequalRankIntegrand_mk, hzero]

/-- Fixed-rank coefficients inherit the actual lower-support bound. -/
theorem strictSliceCoefficient_lowerSupport
    (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (f : (coefficientModel π lambda).toSubmodule)
    (Wjac : InverseWhittakerFunctions ψ n) :
    HasLowerBoundedSupport (strictSliceCoefficient F hr ψ μ ν f.val Wjac) := by
  subst r
  exact unequalRankSliceCoefficient_lowerSupport F ψ μ
    (strictRectangleMeasure F ν j (n + 1)) π hπ lambda f Wjac

end Langlands.AllField.RankinSelberg.DominantRankTransport

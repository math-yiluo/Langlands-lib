import Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof
import Langlands.Representation.RankinSelberg.UnequalRankDeterminantSlices
import Langlands.Representation.RankinSelberg.TwistInvariance
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# Actual strictly dominant coefficient support

The support argument uses only the smooth larger Whittaker coefficient.
Convergence and the two first-block Laurent identities remain separate.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance strictCoefficientTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictCoefficientValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictCoefficientLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictCoefficientT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance strictCoefficientSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictCoefficientMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictCoefficientBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictCoefficientQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictCoefficientQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

variable {n r j k : ℕ}

/-- The supplied scalar Haar's rectangle product, with only its measurable
space identified with the canonical Borel space. -/
def strictRectangleMeasure (ν : AdditiveHaarMeasure F.Carrier) (a b : ℕ) :
    @Measure (Matrix (Fin a) (Fin b) F.Carrier) (borel _) :=
  (show (inferInstance : MeasurableSpace (Matrix (Fin a) (Fin b) F.Carrier)) =
      borel _ from
    @BorelSpace.measurable_eq _ _ _
      (inferInstanceAs (BorelSpace (Fin a → Fin b → F.Carrier)))) ▸
    rectangularMeasure ν a b

/-- Fixed larger rank wrapper for the actual unequal-rank slice coefficient. -/
def strictSliceCoefficient (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier)
    (Wtest : WhittakerFunctions ψ r) (Wjac : InverseWhittakerFunctions ψ n) :
    BilateralLaurentSeries :=
  unequalRankSliceCoefficient F j k ψ μ
    (strictRectangleMeasure F ν j (n + 1)) (hr ▸ Wtest) Wjac

/-- The unequal-rank coefficients have a finite negative tail. No assumption
on the smaller Whittaker function or either supplied measure is needed. -/
theorem unequalRankSliceCoefficient_lowerSupport
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ν : @Measure (Matrix (Fin j) (Fin (n + 1)) F.Carrier) (borel _))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsSmooth π)
    (lambda : glFunctionals ψ (n + (j + k + 1)) π)
    (f : (coefficientModel π lambda).toSubmodule)
    (Wjac : InverseWhittakerFunctions ψ n) :
    HasLowerBoundedSupport
      (unequalRankSliceCoefficient F j k ψ μ ν f.val Wjac) := by
  obtain ⟨R, hR, hroot⟩ := Whittaker.smoothSimpleRootSupport F
    F.canonicalTopologicalData (n + (j + k + 1)) ψ V π hπ lambda f
  have hq : (1 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one
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
          F.canonicalTopologicalData.normalizedAbs
            (lastRow (unequalRankMatrix j k g x) b) ≤ 1 := by
        rw [lastRow, unequalRankMatrix_val]
        simp [appendIdentity_entry, rectangularEntries, Fin.val_last,
          show ¬n + (j + k + 1) < n + 1 by omega,
          show ¬n + (j + k + 1) < n + 1 + j by omega]
        split_ifs <;> simp [F.canonicalTopologicalData.normalizedAbs_one,
          F.canonicalTopologicalData.normalizedAbs_zero]
      have hdet := normalizedAbs_determinant_le_of_simpleRoot
        F.canonicalTopologicalData (n + (j + k + 1)) ψ f.val hR zero_le_one
        hroot (unequalRankMatrix j k g x) hnonzero hrow
      rw [determinant_unequalRankMatrix,
        F.canonicalTopologicalData.normalizedAbs_of_ne_zero
          (GeneralLinear.determinant g).ne_zero, hqd] at hdet
      have hle :
          (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (N : ℤ) ≤
            (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (-d) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_natCast] at hle
      linarith
    simp [unequalRankIntegrand_mk, hzero]

/-- Fixed-rank coefficients inherit the actual lower-support bound. -/
theorem strictSliceCoefficient_lowerSupport
    (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient n F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (f : (coefficientModel π lambda).toSubmodule)
    (Wjac : InverseWhittakerFunctions ψ n) :
    HasLowerBoundedSupport (strictSliceCoefficient F hr ψ μ ν f.val Wjac) := by
  subst r
  exact unequalRankSliceCoefficient_lowerSupport F ψ μ
    (strictRectangleMeasure F ν j (n + 1)) π hπ lambda f Wjac

end Langlands.RankinSelberg.DominantRankTransport

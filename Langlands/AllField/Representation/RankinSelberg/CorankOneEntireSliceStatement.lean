import Langlands.Representation.RankinSelberg.CorankOneEntireSliceStatement
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
/-!
# Entire dependence of corank-one determinant-slice coefficients

A derived prerequisite extracted from the uniform-level and determinant-slice
argument of JPSS (1983), Section 4.5, printed pages 408–409, in the corank-one
setting relevant to Section 6.1/6.3, printed pages 427–438. This module defines
the proposition only; it does not prove integrability or analyticity.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CorankOneEntireSliceStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

/-- Every determinant slice of a common-level, pointwise entire family of
standard Whittaker functions on `GL_(r+2)`, paired with a fixed inverse-character
coefficient of a full Whittaker-type representation on `GL_(r+1)`, is integrable
and has an entire coefficient. This is a closed proposition, not a proof. -/
def CorankOneEntireSliceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (r : ℕ),
      letI := borel (Langlands.GeneralLinear (r + 1) F)
      letI : BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
      letI := borel (upperUnipotent (r + 1) F)
      letI : BorelSpace (upperUnipotent (r + 1) F) := ⟨rfl⟩
      letI := borel (LeftUnipotentQuotient r F)
      letI : BorelSpace (LeftUnipotentQuotient r F) := ⟨rfl⟩
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F r)],
      ∀ ν : Measure (LeftUnipotentQuotient r F),
        IsCompatible (upperUnipotent (r + 1) F)
          (generalLinearHaar F r) (unipotentHaar F r) ν →
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V),
          IsOfWhittakerType r (inverseStandardCharacter ψ r) τ →
          ∀ (ℓ : glInverseFunctionals ψ r τ)
            (Wprime : (coefficientModel τ ℓ).toSubmodule)
            (U : ℂ → WhittakerFunctions ψ (r + 1)),
            (∃ K : Subgroup (Langlands.GeneralLinear (r + 1 + 1) F),
              IsOpen (K : Set (Langlands.GeneralLinear (r + 1 + 1) F)) ∧
              IsCompact (K : Set (Langlands.GeneralLinear (r + 1 + 1) F)) ∧
              ∀ (u : ℂ) (g : Langlands.GeneralLinear (r + 1 + 1) F) (k : K),
                (U u).val (g * k) = (U u).val g) →
            (∀ (g : Langlands.GeneralLinear (r + 1 + 1) F) (u : ℂ),
              AnalyticAt ℂ (fun z => (U z).val g) u) →
            ∀ m : ℤ,
              (∀ u : ℂ,
                SliceIntegrableAt (⟨⟩ : LocalFieldData F) ν
                  (corankOneIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
                    (U u) Wprime.val 0) m) ∧
              ∀ u : ℂ,
                AnalyticAt ℂ
                  (fun z => sliceCoefficient (⟨⟩ : LocalFieldData F) ν
                    (corankOneIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
                      (U z) Wprime.val 0) m) u

end Langlands.AllField.RankinSelberg

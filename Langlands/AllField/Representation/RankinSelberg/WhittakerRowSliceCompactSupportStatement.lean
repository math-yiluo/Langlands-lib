import Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
/-!
# Compact support of Whittaker row data on a determinant slice

The compact-support assertion of JPSS (1983), Section 4.6, printed page 412,
for the norm of `W(g) Φ(η g)` on each fixed determinant slice of the actual
quotient `N_(n+1) \ GL_(n+1)`, for actual coefficient images of smooth
representations. This is a proposition definition; no proof is supplied.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV

/-- On every determinant slice, the norm of `W(g) Φ(lastRow g)`, extended by zero
off the slice, has compact support on the actual quotient topology. The scope is
every actual coefficient image of every smooth representation, including zero
functionals, zero coefficients, zero test functions and actual rank one. -/
def WhittakerRowSliceCompactSupportStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V,
      IsSmooth π →
      ∀ ℓ : glFunctionals ψ n π,
        ∀ W : (coefficientModel π ℓ).toSubmodule,
        ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
        ∀ k : ℤ,
          HasCompactSupport
            ((determinantSlice T n k).indicator
              (fun q : LeftUnipotentQuotient n F =>
                whittakerNorm ψ W.val q * ‖Φ (quotientLastRow n q)‖))

end Langlands.AllField.RankinSelberg

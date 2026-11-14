import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion
/-!
# Proof of the rank-one JPSS comparison `I₁ = I₃`

The case `n = 0` is `rankOneMatrixWhittakerComparison_zero`. For `n = m + 1` both
value sets equal the reduced `GL₁` value set `rankOneModelValues`: the left one by
`characterZetaValues_one_succ_eq`, the right one by the two inclusions
`RankOneIwasawa.whittakerRationalValues_subset_rankOneModelValues` and
`rankOneModelValues_subset_whittakerRationalValues`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneMatrixWhittakerComparisonStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map exists_rankOneCutoff exists_rankOneEmbedding_support lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues singleton_modulus_real whittakerRationalValues_eq_rankOneModelValues zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

/-- The comparison statement follows from the positive-rank identification of the
matrix–Whittaker values with the reduced `GL₁` values. -/
theorem rankOneMatrixWhittakerComparison_of_positive
    (hpos : ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
      (ψ : UnitaryAdditiveCharacter F)
      (m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V),
      letI := borel (Langlands.GeneralLinear (0 + 1) F)
      letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
      IsSmooth σ → ∀ ℓ : glFunctionals ψ (m + 1) σ,
        Langlands.AllField.GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ =
          rankOneModelValues (⟨⟩ : LocalFieldData F).residueCardinality ψ
            (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            (generalLinearHaar F 0) σ ℓ) :
    RankOneMatrixWhittakerComparisonStatement.{uF, uV} := by
  intro F _ _ _ _ ψ n V _ _ σ
  cases n with
  | zero => exact rankOneMatrixWhittakerComparison_zero F ψ V σ
  | succ m =>
    intro hσ ℓ hℓ _ μ hμ
    let := borel (Langlands.GeneralLinear (0 + 1) F)
    have : BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
    let := borel (upperUnipotent (0 + 1) F)
    have : BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
    let := borel (LeftUnipotentQuotient 0 F)
    have : BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩
    rw [characterZetaValues_one_succ_eq _ ψ _ hσ ℓ hℓ μ hμ]
    exact congrArg zetaSpan (hpos F ψ m V σ hσ.1.1 ℓ).symm

/-- The positive-rank identification of the matrix–Whittaker values with the reduced
`GL₁` values. -/
theorem whittakerRationalValues_eq_rankOneModelValues 
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V) :
    letI := borel (Langlands.GeneralLinear (0 + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F) := ⟨rfl⟩
    IsSmooth σ → ∀ ℓ : glFunctionals ψ (m + 1) σ,
      Langlands.AllField.GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ =
        rankOneModelValues (⟨⟩ : LocalFieldData F).residueCardinality ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          (generalLinearHaar F 0) σ ℓ :=
  fun hσ ℓ => Set.Subset.antisymm
    (Langlands.AllField.RankinSelberg.RankOneIwasawa.whittakerRationalValues_subset_rankOneModelValues F ψ σ hσ ℓ)
    (rankOneModelValues_subset_whittakerRationalValues F ψ m V σ hσ ℓ)

/-- **The rank-one JPSS comparison `I₁ = I₃`.** -/
theorem rankOneMatrixWhittakerComparison :
    RankOneMatrixWhittakerComparisonStatement.{uF, uV} :=
  rankOneMatrixWhittakerComparison_of_positive whittakerRationalValues_eq_rankOneModelValues

end Langlands.AllField.RankinSelberg

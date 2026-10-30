import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonStatement
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonZero
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonLeft
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox

/-!
# Proof of the rank-one JPSS comparison `I₁ = I₃`

The case `n = 0` is `rankOneMatrixWhittakerComparison_zero`. For `n = m + 1` both
value sets equal the reduced `GL₁` value set `rankOneModelValues`: the left one by
`characterZetaValues_one_succ_eq`, the right one by the two inclusions
`RankOneIwasawa.whittakerRationalValues_subset_rankOneModelValues` and
`rankOneModelValues_subset_whittakerRationalValues`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-- The comparison statement follows from the positive-rank identification of the
matrix–Whittaker values with the reduced `GL₁` values. -/
theorem rankOneMatrixWhittakerComparison_of_positive
    (hpos : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
      (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
      (m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V),
      letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
      letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
      IsSmooth σ → ∀ ℓ : glFunctionals ψ (m + 1) σ,
        GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ =
          rankOneModelValues F.canonicalTopologicalData.residueCardinality ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData)
            (generalLinearHaar F.Carrier 0) σ ℓ) :
    RankOneMatrixWhittakerComparisonStatement.{uF, uV} := by
  intro p _ F ψ n V _ _ σ
  cases n with
  | zero => exact rankOneMatrixWhittakerComparison_zero p F ψ V σ
  | succ m =>
    intro hσ ℓ hℓ _ μ hμ
    let := F.canonicalTopologicalData.topology
    let := F.canonicalTopologicalData.valuativeRel
    let := F.canonicalTopologicalData.localField
    let := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
    have : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
    let := borel (upperUnipotent (0 + 1) F.Carrier)
    have : BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
    let := borel (LeftUnipotentQuotient 0 F.Carrier)
    have : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩
    rw [characterZetaValues_one_succ_eq _ ψ _ hσ ℓ hℓ μ hμ]
    exact congrArg zetaSpan (hpos p F ψ m V σ hσ.1.1 ℓ).symm

/-- The positive-rank identification of the matrix–Whittaker values with the reduced
`GL₁` values. -/
theorem whittakerRationalValues_eq_rankOneModelValues (p : ℕ) [Fact p.Prime]
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (m : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) V) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (Langlands.GeneralLinear (0 + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (0 + 1) F.Carrier) := ⟨rfl⟩
    IsSmooth σ → ∀ ℓ : glFunctionals ψ (m + 1) σ,
      GodementJacquet.Padic.whittakerRationalValues F ψ σ ℓ =
        rankOneModelValues F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData)
          (generalLinearHaar F.Carrier 0) σ ℓ :=
  fun hσ ℓ => Set.Subset.antisymm
    (RankOneIwasawa.whittakerRationalValues_subset_rankOneModelValues F ψ σ hσ ℓ)
    (rankOneModelValues_subset_whittakerRationalValues p F ψ m V σ hσ ℓ)

/-- **The rank-one JPSS comparison `I₁ = I₃`.** -/
theorem rankOneMatrixWhittakerComparison :
    RankOneMatrixWhittakerComparisonStatement.{uF, uV} :=
  rankOneMatrixWhittakerComparison_of_positive whittakerRationalValues_eq_rankOneModelValues

end Langlands.RankinSelberg

import Langlands.Representation.RankinSelberg.GammaFactor

/-! Paired complementary-block transfer target derived from JPSS §2.8. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The valuation topology has a basis of open additive subgroups. This
bridges existing Mathlib classes without adding a hypothesis to the targets. -/
private theorem complementaryTransfer_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- For every adjacent pair of blocks, one coefficient in the original model
transfers both actual integral functions on respective right half-planes.
This derived interface asserts no functional equation or continuation. -/
def UnequalRankComplementaryTransferStatement (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := complementaryTransfer_nonarchimedean (K := F.Carrier)
  letI := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  ∀ hnr : n < r,
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ν : AdditiveHaarMeasure F.Carrier, IsSelfDual ψ ν →
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
      ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
      ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
        IsOfWhittakerType r (standardCharacter ψ r) π →
        IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
        ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
          ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
          ∀ (j k : ℕ) (hr : r = n + (j + k + 2)),
          ∀ f : (coefficientModel π ℓ).toSubmodule,
          ∀ f' : (coefficientModel σ ℓ').toSubmodule,
            ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
            ∃ a b : ℝ,
              (∀ s : ℂ, a < s.re →
                unequalRankIntegralAt (j + 1) k (by omega) ψ
                    (normalizedAbsoluteValue T) μ
                    (rectangularMeasure ν (j + 1) (n + 1)) f.val f'.val s =
                  unequalRankIntegralAt j (k + 1) (by omega) ψ
                    (normalizedAbsoluteValue T) μ
                    (rectangularMeasure ν j (n + 1)) f₀.val f'.val s) ∧
              (∀ s : ℂ, b < s.re →
                dualUnequalRankModelIntegralAt hnr (j + 1) k (by omega) ψ
                    (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' f f' s =
                  dualUnequalRankModelIntegralAt hnr j (k + 1) (by omega) ψ
                    (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' f₀ f' s)

end Langlands.RankinSelberg

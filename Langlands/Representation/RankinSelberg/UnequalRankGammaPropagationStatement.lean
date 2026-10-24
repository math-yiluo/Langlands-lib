import Langlands.Representation.RankinSelberg.GammaFactor

/-! Same-multiplier propagation from block zero, as a derived JPSS §2.8 target. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The valuation topology has a basis of open additive subgroups. This
bridges existing Mathlib classes without adding a hypothesis to the targets. -/
private theorem propagation_nonarchimedean {K : Type uF} [Field K]
    [TopologicalSpace K] [ValuativeRel K] [IsValuativeTopology K] :
    NonarchimedeanAddGroup K where
  is_nonarchimedean U hU := by
    obtain ⟨S, hS, hSU⟩ :=
      (IsLinearTopology.hasBasis_open_submodule
        (ValuativeRel.valuation K).integer (M := K)).mem_iff.mp hU
    exact ⟨⟨S.toAddSubgroup, hS⟩, hSU⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The actual block-zero gamma equation for a given rational function `G`
propagates to every complementary block with that same `G`. This proposition
is the derived prerequisite corresponding to JPSS §2.8; it is not proved here. -/
def UnequalRankGammaPropagationStatement (n r : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  letI := propagation_nonarchimedean (K := F.Carrier)
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
          ∀ G : RationalFunctions,
            (∃ ζ : ℂˣ, HasModelMinusOneScalar σ ℓ' ζ ∧
              (∃ R ∈ unequalRankValuesAt 0 (r - n - 1) (by omega)
                  T.residueCardinality ψ (normalizedAbsoluteValue T) μ
                  (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ', R ≠ 0) ∧
              ∀ f : (coefficientModel π ℓ).toSubmodule,
              ∀ f' : (coefficientModel σ ℓ').toSubmodule,
                ∃ R Rdual : RationalFunctions,
                  HasRationalContinuation T.residueCardinality
                    (unequalRankIntegralAt 0 (r - n - 1) (by omega) ψ
                      (normalizedAbsoluteValue T) μ (rectangularMeasure ν 0 (n + 1))
                      f.val f'.val) R ∧
                  HasRationalContinuation T.residueCardinality
                    (dualUnequalRankModelIntegralAt hnr 0 (r - n - 1) (by omega) ψ
                      (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' f f') Rdual ∧
                  GammaFunctionalEquation T.residueCardinality ζ r G R Rdual) →
            UnequalRankGammaEquation hnr T.residueCardinality ψ
              (normalizedAbsoluteValue T) μ ν π σ ℓ ℓ' G

end Langlands.RankinSelberg

import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement
import Langlands.Representation.RankinSelberg.UnequalRankGammaPropagationStatement
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement
import Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof
import Langlands.Representation.RankinSelberg.UnequalRankComplementaryTransferProof

/-! Same-multiplier propagation from the published paired transfer and
adjacent-span proofs, retaining the actual coefficient-model integrals. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- Equality of Laurent spans transports existence of a nonzero member. -/
private theorem propagation_nonzero_of_zetaSpan_eq
    {S T : Set RationalFunctions} (hst : zetaSpan S = zetaSpan T)
    (hT : ∃ R ∈ T, R ≠ 0) : ∃ R ∈ S, R ≠ 0 := by
  classical
  by_contra! hS
  have hbot : zetaSpan S = ⊥ := by
    rw [zetaSpan, Submodule.span_eq_bot]
    exact hS
  obtain ⟨R, hR, hR0⟩ := hT
  have hm : R ∈ zetaSpan S := by
    rw [hst]
    exact mem_zetaSpan hR
  rw [hbot, Submodule.mem_bot] at hm
  exact hR0 hm

section FixedData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {hnr : n < r} {q : ℕ} {ψ : UnitaryAdditiveCharacter F}
  {abv : AbsoluteValue F ℝ} {μ : Measure (LeftUnipotentQuotient n F)}
  {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

/-- A paired transfer preserves the rational functions themselves, so induction
on the first block retains the supplied gamma multiplier. -/
theorem unequalRankGammaEquation_of_pairedTransfer
    (hSpan : ∀ (j k : ℕ) (hr : r = n + (j + k + 2)),
      zetaSpan
        (unequalRankValuesAt (j + 1) k (by omega) q ψ abv μ
          (rectangularMeasure ν (j + 1) (n + 1)) π σ ℓ ℓ') =
      zetaSpan
        (unequalRankValuesAt j (k + 1) (by omega) q ψ abv μ
          (rectangularMeasure ν j (n + 1)) π σ ℓ ℓ'))
    (hTransfer : ∀ (j k : ℕ) (hr : r = n + (j + k + 2)),
      ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∀ f' : (coefficientModel σ ℓ').toSubmodule,
        ∃ f₀ : (coefficientModel π ℓ).toSubmodule,
        ∃ a b : ℝ,
          (∀ s : ℂ, a < s.re →
            unequalRankIntegralAt (j + 1) k (by omega) ψ abv μ
                (rectangularMeasure ν (j + 1) (n + 1)) f.val f'.val s =
              unequalRankIntegralAt j (k + 1) (by omega) ψ abv μ
                (rectangularMeasure ν j (n + 1)) f₀.val f'.val s) ∧
          (∀ s : ℂ, b < s.re →
            dualUnequalRankModelIntegralAt hnr (j + 1) k (by omega) ψ
                abv μ ν π σ ℓ ℓ' f f' s =
              dualUnequalRankModelIntegralAt hnr j (k + 1) (by omega) ψ
                abv μ ν π σ ℓ ℓ' f₀ f' s))
    {G : RationalFunctions}
    (hZero : UnequalRankBlockZeroGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G) :
    UnequalRankGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G := by
  obtain ⟨ζ, hζ, hNonzero, hEquation⟩ := hZero
  refine ⟨ζ, hζ, ?_⟩
  intro j
  induction j with
  | zero =>
      intro k hr
      have hk : k = r - n - 1 := by omega
      subst k
      exact ⟨hNonzero, hEquation⟩
  | succ j ih =>
      intro k hr
      have hPrevious := ih (k + 1) (by omega)
      refine ⟨propagation_nonzero_of_zetaSpan_eq (hSpan j k (by omega))
        hPrevious.1, ?_⟩
      intro f f'
      obtain ⟨f₀, a, b, hOriginal, hDual⟩ := hTransfer j k (by omega) f f'
      obtain ⟨R, Rdual, hR, hRdual, hGamma⟩ := hPrevious.2 f₀ f'
      exact ⟨R, Rdual, RationalContinuationLinear.continuation_of_eq_on_right hR ⟨a, hOriginal⟩,
        RationalContinuationLinear.continuation_of_eq_on_right hRdual ⟨b, hDual⟩, hGamma⟩

end FixedData

section PadicAssembly

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The literal block-zero gamma equation propagates to all complementary
blocks with the same supplied rational multiplier and the same measures. -/
theorem unequalRankGammaPropagation (n r : ℕ) :
    UnequalRankGammaPropagationStatement.{uF, uV, uW} F T n r := by
  have hTransfer := unequalRankComplementaryTransfer.{uF, uV, uW} F T n r
  have hSpan := unequalRankAdjacentBlockSpan.{uF, uV, uW} F T n r
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let := rowFourierCutoff_nonarchimedean (K := F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro hnr ψ hInv μ hμ ν hν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' G hZero
  exact unequalRankGammaEquation_of_pairedTransfer
    (hSpan hnr ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ')
    (hTransfer hnr ψ μ hμ ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ') hZero

end PadicAssembly

end Langlands.RankinSelberg

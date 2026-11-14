import Langlands.Representation.RankinSelberg.SingleBlockFactors
import Langlands.AllField.Representation.Induction.SingleBlockSupplement
import Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply singleBlock_L_iff singleBlock_gamma_iff succSingleBlockNormalizedProductEquiv
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

variable (F : Type uF) [Field F]
  (m : Fin 1 → ℕ)
  {W : Fin 1 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))

/-- For the successor-rank convention, single-block evaluation has no residual rank cast. -/
def succSingleBlockNormalizedProductEquiv [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (hσ : ∀ i, IsSmooth (σ i)) :
    ((⟨⟩ : LocalFieldData F).normalizedProductInduced
      (succBlockShape m (show ∑ i, (m i + 1) = m 0 + 1 by simp)) σ).Equiv (σ 0) := by
  let B := succBlockShape m (show ∑ i, (m i + 1) = m 0 + 1 by simp)
  let e := (⟨⟩ : LocalFieldData F).singleBlockNormalizedProductEquiv B rfl σ hσ 0
  refine e.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ (W 0)) ?_)
  intro g
  have hg :
      (GeneralLinear.reindex (R := F) (finCongr (B.singleBlock_size rfl 0))).symm g = g := by
    apply Units.ext
    ext a b
    rfl
  change (σ 0) ((GeneralLinear.reindex (R := F)
    (finCongr (B.singleBlock_size rfl 0))).symm g) = (σ 0) g
  rw [hg]

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {ψ : UnitaryAdditiveCharacter F}
  {ν : letI := borel F
    AdditiveHaarMeasure F}
  {r t : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)

/-- A supplied gamma certificate transports to the actual one-block induction. -/
theorem singleBlock_gamma_iff
    (h : ∑ i, (m i + 1) = t + 1)
    (hσ : ∀ i, IsSmooth (σ i))
    {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) G ↔
      IsPadicSymmetricGammaFactor F ψ ν π (σ 0) G := by
  have ht : t = m 0 := by simpa using h.symm
  subst t
  exact Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl π)
    (succSingleBlockNormalizedProductEquiv F m σ hσ)

/-- A supplied L-polynomial certificate transports to the actual one-block induction. -/
theorem singleBlock_L_iff
    (h : ∑ i, (m i + 1) = t + 1)
    (hσ : ∀ i, IsSmooth (σ i))
    {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν π
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ) P ↔
      IsPadicSymmetricLPolynomial F ψ ν π (σ 0) P := by
  have ht : t = m 0 := by simpa using h.symm
  subst t
  exact Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl π)
    (succSingleBlockNormalizedProductEquiv F m σ hσ)

end Langlands.AllField.RankinSelberg

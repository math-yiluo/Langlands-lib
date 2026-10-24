import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.RankinSelberg.MultiplicativityStatement

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (m : Fin 1 → ℕ)
  {W : Fin 1 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

/-- For the successor-rank convention, single-block evaluation has no residual rank cast. -/
def succSingleBlockNormalizedProductEquiv
    (hσ : letI := F.canonicalTopologicalData.topology; ∀ i, IsSmooth (σ i)) :
    (F.canonicalNormalizedProductInduced
      (succBlockShape m (show ∑ i, (m i + 1) = m 0 + 1 by simp)) σ).Equiv (σ 0) := by
  let B := succBlockShape m (show ∑ i, (m i + 1) = m 0 + 1 by simp)
  let e := F.canonicalTopologicalData.singleBlockNormalizedProductEquiv B rfl σ hσ 0
  refine e.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ (W 0)) ?_)
  intro g
  have hg :
      (GeneralLinear.reindex (R := F.Carrier) (finCongr (B.singleBlock_size rfl 0))).symm g = g := by
    apply Units.ext
    ext a b
    rfl
  change (σ 0) ((GeneralLinear.reindex (R := F.Carrier)
    (finCongr (B.singleBlock_size rfl 0))).symm g) = (σ 0) g
  rw [hg]

variable
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r t : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)

/-- A supplied gamma certificate transports to the actual one-block induction. -/
theorem singleBlock_gamma_iff
    (h : ∑ i, (m i + 1) = t + 1)
    (hσ : letI := F.canonicalTopologicalData.topology; ∀ i, IsSmooth (σ i))
    {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) G ↔
      IsPadicSymmetricGammaFactor F ψ ν π (σ 0) G := by
  have ht : t = m 0 := by simpa using h.symm
  subst t
  exact IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl π)
    (succSingleBlockNormalizedProductEquiv F m σ hσ)

/-- A supplied L-polynomial certificate transports to the actual one-block induction. -/
theorem singleBlock_L_iff
    (h : ∑ i, (m i + 1) = t + 1)
    (hσ : letI := F.canonicalTopologicalData.topology; ∀ i, IsSmooth (σ i))
    {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P ↔
      IsPadicSymmetricLPolynomial F ψ ν π (σ 0) P := by
  have ht : t = m 0 := by simpa using h.symm
  subst t
  exact IsPadicSymmetricLPolynomial.congr_equiv (Representation.Equiv.refl π)
    (succSingleBlockNormalizedProductEquiv F m σ hσ)

end Langlands.RankinSelberg

import Langlands.Representation.RankinSelberg.PadicTwistedPositiveCoefficients
import Langlands.Representation.RankinSelberg.IntegrandContinuityProof
import Langlands.Analysis.Local.QuotientMass
import Langlands.LocalField.Normalization.Continuity

/-! # Strictly positive equal-rank integrals at a contragredient twist -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)

/-- Some actual paired coefficients have an absolutely convergent equal-rank
integral with strictly positive real part at the indicated twist parameter. -/
def HasPositiveEqualRankIntegral
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (μ : letI := T.topology; letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier))
    (u : ℂ) (ℓ : letI := T.topology; glFunctionals ψ n π)
    (Φ : letI := T.topology; SchwartzBruhat (Fin (n + 1) → F.Carrier)) : Prop :=
  letI := T.topology
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  ∃ m : glInverseFunctionals ψ n σ, m.val ≠ 0 ∧
    ∃ v : V, ∃ w : W,
      EqualRankConverges ψ (normalizedAbsoluteValue T) μ
        (coefficientMap π ℓ v) (coefficientMap σ m w) Φ (-u) ∧
      0 < (equalRankIntegral ψ (normalizedAbsoluteValue T) μ
        (coefficientMap π ℓ v) (coefficientMap σ m w) Φ (-u)).re

/-- A zero-or-one cutoff positive at the identity turns the weighted
squared-norm coefficient package into a strictly positive actual integral,
provided its actual paired integrands converge at the specified parameter. -/
theorem HasPadicTwistedPositiveCoefficients.hasPositiveEqualRankIntegral
    {ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier}
    {μ : letI := T.topology; letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier)}
    {u : ℂ} {ℓ : letI := T.topology; glFunctionals ψ n π}
    (h : HasPadicTwistedPositiveCoefficients T π σ ψ u ℓ) (hℓ : ℓ.val ≠ 0) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    μ.IsOpenPosMeasure → IsSmooth π → IsSmooth σ →
      ∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
        Φ (lastRow (1 : Langlands.GeneralLinear (n + 1) F.Carrier)) = 1 →
        (∀ x, Φ x = 0 ∨ Φ x = 1) →
        (∀ (m : glInverseFunctionals ψ n σ) (v : V) (w : W),
          EqualRankConverges ψ (normalizedAbsoluteValue T) μ
            (coefficientMap π ℓ v) (coefficientMap σ m w) Φ (-u)) →
        HasPositiveEqualRankIntegral T π σ ψ μ u ℓ Φ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro hμ hπ hσ Φ hΦ1 hΦ hconv
  let : μ.IsOpenPosMeasure := hμ
  obtain ⟨t, _, m, hm, hpair⟩ := h
  obtain ⟨v, hv⟩ : ∃ v : V, ℓ.val v ≠ 0 := by
    by_contra hzero
    apply hℓ
    ext v
    exact not_not.mp (not_exists.mp hzero v)
  obtain ⟨w, hw⟩ := hpair v
  let f := equalRankIntegrand ψ (normalizedAbsoluteValue T)
    (coefficientMap π ℓ v) (coefficientMap σ m w) Φ (-u)
  have hfcont : Continuous f :=
    equalRankIntegrandContinuous F.Carrier n (normalizedAbsoluteValue T)
      T.continuous_normalizedAbs V W π σ hπ hσ ψ ℓ m
      (modelMap π ℓ v) (modelMap σ m w) Φ (-u)
  have hfint : Integrable f μ := hconv m v w
  have heq (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
      f (Quotient.mk _ g) =
        ((‖ℓ.val (realPowerTwist (T.determinantNorm (n + 1)) t π g v)‖ ^ 2 : ℝ) : ℂ) *
          Φ (lastRow g) := by
    change _ * _ * _ * _ = _
    calc
      _ = (determinantWeight (normalizedAbsoluteValue T) g (-u) *
          ((coefficientMap π ℓ v).val g * (coefficientMap σ m w).val g)) *
          Φ (lastRow g) := by ring
      _ = _ := by rw [hw]
  have hfnonneg : ∀ q, 0 ≤ (f q).re := by
    intro q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [heq g]
      rcases hΦ (lastRow g) with hzero | hone
      · simp only [hzero, mul_zero, Complex.zero_re, le_refl]
      · simpa only [hone, mul_one, Complex.ofReal_re] using
          sq_nonneg ‖ℓ.val (realPowerTwist (T.determinantNorm (n + 1)) t π g v)‖
  have hf1 : 0 < (f (Quotient.mk _ 1)).re := by
    rw [heq, hΦ1, mul_one]
    simpa only [map_one, Module.End.one_apply, Complex.ofReal_re] using
      sq_pos_of_pos (norm_pos_iff.mpr hv)
  refine ⟨m, hm, v, w, hfint, ?_⟩
  change 0 < RCLike.re (∫ q, f q ∂μ)
  rw [← integral_re hfint]
  exact integral_pos_of_integrable_nonneg_nonzero (x := Quotient.mk _ 1)
    (Complex.continuous_re.comp hfcont) hfint.re hfnonneg (ne_of_gt hf1)

/-- Compact support and a measure finite on compact sets discharge actual
convergence in the preceding positivity criterion. -/
theorem HasPadicTwistedPositiveCoefficients.hasPositiveEqualRankIntegral_of_compactSupport
    {ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier}
    {μ : letI := T.topology; letI := borel (LeftUnipotentQuotient n F.Carrier)
      Measure (LeftUnipotentQuotient n F.Carrier)}
    {u : ℂ} {ℓ : letI := T.topology; glFunctionals ψ n π}
    (h : HasPadicTwistedPositiveCoefficients T π σ ψ u ℓ) (hℓ : ℓ.val ≠ 0) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    μ.IsOpenPosMeasure → IsFiniteMeasureOnCompacts μ → IsSmooth π → IsSmooth σ →
      ∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
        Φ (lastRow (1 : Langlands.GeneralLinear (n + 1) F.Carrier)) = 1 →
        (∀ x, Φ x = 0 ∨ Φ x = 1) →
        (∀ (m : glInverseFunctionals ψ n σ) (v : V) (w : W),
          HasCompactSupport (equalRankIntegrand ψ (normalizedAbsoluteValue T)
            (coefficientMap π ℓ v) (coefficientMap σ m w) Φ (-u))) →
        HasPositiveEqualRankIntegral T π σ ψ μ u ℓ Φ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro hμ hμc hπ hσ Φ hΦ1 hΦ hc
  let : IsFiniteMeasureOnCompacts μ := hμc
  apply h.hasPositiveEqualRankIntegral T π σ hℓ hμ hπ hσ Φ hΦ1 hΦ
  intro m v w
  exact (equalRankIntegrandContinuous F.Carrier n (normalizedAbsoluteValue T)
    T.continuous_normalizedAbs V W π σ hπ hσ ψ ℓ m
    (modelMap π ℓ v) (modelMap σ m w) Φ (-u)).integrable_of_hasCompactSupport
      (hc m v w)

end Langlands.RankinSelberg

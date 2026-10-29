import Langlands.Representation.RankinSelberg.SquareIntegrableEqualRankAnalyticStatement
import Langlands.Representation.RankinSelberg.IntegrandContinuityProof
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Langlands.Representation.RankinSelberg.WeightedWhittakerSquareProof
import Langlands.Analysis.MellinHalfPlaneProof
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Square-integrable equal-rank convergence and holomorphy

The two published weighted-square estimates dominate the actual quotient integrand.
The published Mellin theorem then gives complex differentiability on `Re(s) > 0`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The square root of the norm of a test is again a test. -/
private def sqrtNormTest {X : Type*} [TopologicalSpace X]
    (Φ : SchwartzBruhat X) : SchwartzBruhat X :=
  ⟨fun x => (Real.sqrt ‖Φ x‖ : ℂ), by
    constructor
    · exact Φ.locallyConstant.comp (fun z : ℂ => (Real.sqrt ‖z‖ : ℂ))
    · exact Φ.hasCompactSupport.comp_left
        (g := fun z : ℂ => (Real.sqrt ‖z‖ : ℂ))
        (by simp only [norm_zero, Real.sqrt_zero, Complex.ofReal_zero])⟩

private theorem norm_sqrtNormTest_sq {X : Type*} [TopologicalSpace X]
    (Φ : SchwartzBruhat X) (x : X) : ‖sqrtNormTest Φ x‖ ^ 2 = ‖Φ x‖ := by
  change ‖(Real.sqrt ‖Φ x‖ : ℂ)‖ ^ 2 = ‖Φ x‖
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (norm_nonneg _)

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The actual quotient integrand is a positive-weight Mellin integrand. -/
private theorem equalRank_integrand_eq_mellin
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (s : ℂ) (q : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv W W' Φ s q =
      equalRankIntegrand ψ abv W W' Φ 0 q *
        (quotientDeterminantAbs abv n q : ℂ) ^ s := by
  induction q using Quotient.inductionOn with
  | h g => simp [equalRankIntegrand_mk, determinantWeight]

private theorem quotientDet_continuous [IsTopologicalRing F] {n : ℕ}
    (abv : AbsoluteValue F ℝ) (habv : Continuous abv) :
    Continuous (quotientDeterminantAbs abv n) := by
  apply (leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  have hdet : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      abv (Matrix.det g.val)) := habv.comp Units.continuous_val.matrix_det
  change Continuous (fun g => quotientDeterminantAbs abv n (Quotient.mk _ g))
  simpa only [quotientDeterminantAbs_mk] using hdet

private theorem norm_equalRank_integrand
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (q : LeftUnipotentQuotient n F) :
    ‖equalRankIntegrand ψ abv W W' Φ s q‖ =
      whittakerNorm ψ W q * inverseWhittakerNorm ψ W' q *
        ‖Φ (quotientLastRow n q)‖ * (quotientDeterminantAbs abv n q) ^ s.re := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [equalRankIntegrand_mk, norm_mul, determinantWeight,
      Complex.norm_cpow_eq_rpow_re_of_pos (abv.pos g.det_ne_zero),
      whittakerNorm_mk, inverseWhittakerNorm_mk, quotientLastRow_mk,
      quotientDeterminantAbs_mk]

/-- Two actual single-representation square weights dominate the equal-rank
integrand. Measurability is separate from the analytic square estimates. -/
private theorem equalRank_converges_of_weighted_squares
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (hAi : Integrable (fun q => (whittakerNorm ψ W q) ^ 2 *
      ‖Φ (quotientLastRow n q)‖ * (quotientDeterminantAbs abv n q) ^ s.re) μ)
    (hBi : Integrable (fun q => (inverseWhittakerNorm ψ W' q) ^ 2 *
      ‖Φ (quotientLastRow n q)‖ * (quotientDeterminantAbs abv n q) ^ s.re) μ)
    (hf : AEStronglyMeasurable (equalRankIntegrand ψ abv W W' Φ s) μ) :
    EqualRankConverges ψ abv μ W W' Φ s := by
  apply ((hAi.add hBi).div_const 2).mono' hf
  apply Filter.Eventually.of_forall
  intro q
  change ‖equalRankIntegrand ψ abv W W' Φ s q‖ ≤
    ((whittakerNorm ψ W q) ^ 2 * ‖Φ (quotientLastRow n q)‖ *
        (quotientDeterminantAbs abv n q) ^ s.re +
      (inverseWhittakerNorm ψ W' q) ^ 2 * ‖Φ (quotientLastRow n q)‖ *
        (quotientDeterminantAbs abv n q) ^ s.re) / 2
  rw [norm_equalRank_integrand]
  have ht : 0 ≤ ‖Φ (quotientLastRow n q)‖ *
      (quotientDeterminantAbs abv n q) ^ s.re :=
    mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (quotientDeterminantAbs_nonneg abv n q) _)
  nlinarith [mul_nonneg
    (sq_nonneg (whittakerNorm ψ W q - inverseWhittakerNorm ψ W' q)) ht]

/-- Apply the two requested square estimates to the square-root norm test.
The square-root identity gives exactly the required single test norm. -/
private theorem equalRank_converges_of_test_weighted_squares
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (hAi : Integrable (fun q => (whittakerNorm ψ W q) ^ 2 *
      ‖sqrtNormTest Φ (quotientLastRow n q)‖ ^ 2 *
        (quotientDeterminantAbs abv n q) ^ (2 * (s.re / 2))) μ)
    (hBi : Integrable (fun q => (inverseWhittakerNorm ψ W' q) ^ 2 *
      ‖sqrtNormTest Φ (quotientLastRow n q)‖ ^ 2 *
        (quotientDeterminantAbs abv n q) ^ (2 * (s.re / 2))) μ)
    (hf : AEStronglyMeasurable (equalRankIntegrand ψ abv W W' Φ s) μ) :
    EqualRankConverges ψ abv μ W W' Φ s := by
  have hexp : 2 * (s.re / 2) = s.re := by ring
  simp only [norm_sqrtNormTest_sq, hexp] at hAi hBi
  exact equalRank_converges_of_weighted_squares ψ abv μ W W' Φ s hAi hBi hf

/-- The published Mellin theorem gives holomorphy of the actual equal-rank
integral from real-axis convergence, with zero shift. -/
private theorem equalRank_holomorphic_of_real_convergence
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hc : AEStronglyMeasurable (equalRankIntegrand ψ abv W W' Φ 0) μ)
    (hd : AEMeasurable (quotientDeterminantAbs abv n) μ)
    (hconv : ∀ t : ℝ, 0 < t →
      EqualRankConverges ψ abv μ W W' Φ (t : ℂ)) :
    DifferentiableOn ℂ (equalRankIntegral ψ abv μ W W' Φ)
      {s : ℂ | 0 < s.re} := by
  have hfactor (s : ℂ) :
      equalRankIntegrand ψ abv W W' Φ s =
        fun q => equalRankIntegrand ψ abv W W' Φ 0 q *
          (quotientDeterminantAbs abv n q : ℂ) ^ s := by
    funext q
    exact equalRank_integrand_eq_mellin ψ abv W W' Φ s q
  have hreal (t : ℝ) (ht : 0 < t) :
      Integrable (fun q => equalRankIntegrand ψ abv W W' Φ 0 q *
        (quotientDeterminantAbs abv n q : ℂ) ^ (t : ℂ)) μ := by
    have hi : Integrable (equalRankIntegrand ψ abv W W' Φ (t : ℂ)) μ := hconv t ht
    rw [hfactor] at hi
    exact hi
  have hm := Langlands.Analysis.mellinHalfPlane (LeftUnipotentQuotient n F) μ
    (equalRankIntegrand ψ abv W W' Φ 0) (quotientDeterminantAbs abv n) 0
    (quotientDeterminantAbs_pos abv n) hc hd
    (by simpa only [Complex.ofReal_zero, sub_zero] using hreal)
  have heq : equalRankIntegral ψ abv μ W W' Φ =
      fun s : ℂ => ∫ q, equalRankIntegrand ψ abv W W' Φ 0 q *
        (quotientDeterminantAbs abv n q : ℂ) ^ s ∂μ := by
    funext s
    unfold equalRankIntegral
    rw [hfactor]
  rw [heq]
  simpa only [Complex.ofReal_zero, sub_zero] using hm

/-- The actual square-integrability hypothesis already supplies every
measurability input needed above, with no assumption on the quotient measure. -/
private theorem squareIntegrable_equalRank_measurable
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier))
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      T.IsSquareIntegrable π → T.IsSquareIntegrable σ →
      ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
        (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
        (f : (coefficientModel π ℓ).toSubmodule)
        (f' : (coefficientModel σ ℓ').toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
        (∀ s : ℂ, AEStronglyMeasurable
          (equalRankIntegrand ψ (normalizedAbsoluteValue T) f.val f'.val Φ s) μ) ∧
        AEMeasurable (quotientDeterminantAbs (normalizedAbsoluteValue T) n) μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro μ V _ _ W _ _ π σ hπ hσ ψ ℓ ℓ' f f' Φ
  have habv : Continuous (normalizedAbsoluteValue T) :=
    NNReal.continuous_coe.comp T.continuous_normalizedAbsHom
  constructor
  · intro s
    exact (equalRankIntegrandContinuous F.Carrier n (normalizedAbsoluteValue T)
      habv V W π σ hπ.isAdmissible.1 hσ.isAdmissible.1
      ψ ℓ ℓ' f f' Φ s).aestronglyMeasurable
  · exact (quotientDet_continuous (normalizedAbsoluteValue T) habv).measurable.aemeasurable

/-- Assemble convergence and holomorphy from the two universe instances of the
weighted-square theorem for the actual coefficient models. -/
private theorem squareIntegrable_equalRank_analytic_of_weighted_squares
    (hSquareV : WeightedWhittakerSquareStatement.{uF, uV})
    (hSquareW : WeightedWhittakerSquareStatement.{uF, uW})
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier),
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
          (W : Type uW) [AddCommGroup W] [Module ℂ W]
          (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
          (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
          Representation.IsIrreducible π → T.IsSquareIntegrable π →
          Representation.IsIrreducible σ → T.IsSquareIntegrable σ →
          ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
            (f : (coefficientModel π ℓ).toSubmodule)
            (f' : (coefficientModel σ ℓ').toSubmodule)
            (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
            (∀ s : ℂ, 0 < s.re →
              EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s) ∧
            DifferentiableOn ℂ
              (equalRankModelIntegral ψ (normalizedAbsoluteValue T) μ π σ ℓ ℓ' f f' Φ)
              {s : ℂ | 0 < s.re} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ _ μ hμ V _ _ W _ _ π σ hπirr hπ hσirr hσ ℓ ℓ' f f' Φ
  obtain ⟨hmeas, hdet⟩ :=
    squareIntegrable_equalRank_measurable F T n μ V W π σ hπ hσ ψ ℓ ℓ' f f' Φ
  have hstandard := (hSquareV p F T n ψ μ hμ V π hπirr hπ).1
  have hinverse := (hSquareW p F T n ψ μ hμ W σ hσirr hσ).2
  have hconv : ∀ s : ℂ, 0 < s.re →
      EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s := by
    intro s hs
    exact equalRank_converges_of_test_weighted_squares ψ (normalizedAbsoluteValue T)
      μ f.val f'.val Φ s
      (hstandard ℓ f (sqrtNormTest Φ) (s.re / 2) (half_pos hs))
      (hinverse ℓ' f' (sqrtNormTest Φ) (s.re / 2) (half_pos hs))
      (hmeas s)
  refine ⟨hconv, ?_⟩
  change DifferentiableOn ℂ
    (equalRankIntegral ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ)
    {s : ℂ | 0 < s.re}
  exact equalRank_holomorphic_of_real_convergence ψ (normalizedAbsoluteValue T) μ
    f.val f'.val Φ (hmeas 0) hdet
    (fun t ht => hconv (t : ℂ) (by simpa only [Complex.ofReal_re] using ht))

/-- Square-integrable irreducible representations give absolutely convergent,
holomorphic actual equal-rank integrals on `Re(s) > 0`. -/
theorem squareIntegrableEqualRankAnalytic :
    SquareIntegrableEqualRankAnalyticStatement.{uF, uV, uW} := by
  intro p _ F T n
  exact squareIntegrable_equalRank_analytic_of_weighted_squares
    weightedWhittakerSquare.{uF, uV} weightedWhittakerSquare.{uF, uW} F T n

end Langlands.RankinSelberg

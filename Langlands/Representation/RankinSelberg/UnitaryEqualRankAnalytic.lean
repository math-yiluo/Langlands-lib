import Langlands.Representation.RankinSelberg.UnitaryWeightedWhittakerSquare
import Langlands.Representation.RankinSelberg.SquareIntegrableEqualRankAnalyticStatement
import Langlands.Representation.RankinSelberg.EqualRankEulerStatement
import Langlands.Representation.RankinSelberg.IntegrandContinuityProof
import Langlands.Analysis.MellinHalfPlaneProof
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Unitary generic equal-rank integrals on `Re(s) ≥ 1`

For irreducible admissible unitarizable representations `π`, `σ` of `GL_(n+1)(F)` over a
p-adic field (canonical topology), standard and inverse Whittaker functionals, coefficient-model
vectors and a Schwartz–Bruhat function, the equal-rank JPSS integral converges absolutely for
`Re(s) ≥ 1` and is holomorphic on `Re(s) > 1`. This is Jacquet–Shalika, *Euler products I*,
Proposition (1.5)(i), together with holomorphy.

The proof is that of the published `squareIntegrableEqualRankAnalytic` with the unitary
weighted square estimate (`unitaryWeightedWhittakerSquare`, valid for `a ≥ 1/2`) in place of
the square-integrable one, and the published Mellin theorem applied with shift `-1`.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnitaryGeneric

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The square root of the norm of a test is again a test. -/
def sqrtNormTest {X : Type*} [TopologicalSpace X]
    (Φ : SchwartzBruhat X) : SchwartzBruhat X :=
  ⟨fun x => (Real.sqrt ‖Φ x‖ : ℂ), by
    constructor
    · exact Φ.locallyConstant.comp (fun z : ℂ => (Real.sqrt ‖z‖ : ℂ))
    · exact Φ.hasCompactSupport.comp_left
        (g := fun z : ℂ => (Real.sqrt ‖z‖ : ℂ))
        (by simp only [norm_zero, Real.sqrt_zero, Complex.ofReal_zero])⟩

theorem norm_sqrtNormTest_sq {X : Type*} [TopologicalSpace X]
    (Φ : SchwartzBruhat X) (x : X) : ‖sqrtNormTest Φ x‖ ^ 2 = ‖Φ x‖ := by
  change ‖(Real.sqrt ‖Φ x‖ : ℂ)‖ ^ 2 = ‖Φ x‖
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (norm_nonneg _)

section General

variable {F : Type uF} [Field F] [TopologicalSpace F]

theorem equalRank_integrand_eq_mellin
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (s : ℂ) (q : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv W W' Φ s q =
      equalRankIntegrand ψ abv W W' Φ 0 q *
        (quotientDeterminantAbs abv n q : ℂ) ^ s := by
  induction q using Quotient.inductionOn with
  | h g => simp [equalRankIntegrand_mk, determinantWeight]

theorem quotientDet_continuous [IsTopologicalRing F] {n : ℕ}
    (abv : AbsoluteValue F ℝ) (habv : Continuous abv) :
    Continuous (quotientDeterminantAbs abv n) := by
  apply (leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  have hdet : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      abv (Matrix.det g.val)) := habv.comp Units.continuous_val.matrix_det
  change Continuous (fun g => quotientDeterminantAbs abv n (Quotient.mk _ g))
  simpa only [quotientDeterminantAbs_mk] using hdet

theorem norm_equalRank_integrand
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

/-- Two single-representation square weights dominate the equal-rank integrand. -/
theorem equalRank_converges_of_weighted_squares
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

/-- The square estimates for the square-root norm test give convergence. -/
theorem equalRank_converges_of_test_weighted_squares
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

/-- The Mellin theorem with shift `-1` gives holomorphy of the equal-rank integral on
`Re(s) > 1` from convergence at every real `t > 1`. -/
theorem equalRank_holomorphic_of_real_convergence_one
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hc : AEStronglyMeasurable (equalRankIntegrand ψ abv W W' Φ 0) μ)
    (hd : AEMeasurable (quotientDeterminantAbs abv n) μ)
    (hconv : ∀ t : ℝ, 1 < t →
      EqualRankConverges ψ abv μ W W' Φ (t : ℂ)) :
    DifferentiableOn ℂ (equalRankIntegral ψ abv μ W W' Φ)
      {s : ℂ | 1 < s.re} := by
  have hfactor (s : ℂ) :
      equalRankIntegrand ψ abv W W' Φ s =
        fun q => equalRankIntegrand ψ abv W W' Φ 0 q *
          (quotientDeterminantAbs abv n q : ℂ) ^ s := by
    funext q
    exact equalRank_integrand_eq_mellin ψ abv W W' Φ s q
  have hshift (w : ℂ) : w - ((-1 : ℝ) : ℂ) = w + 1 := by push_cast; ring
  have hreal (t : ℝ) (ht : 0 < t) :
      Integrable (fun q => equalRankIntegrand ψ abv W W' Φ 0 q *
        (quotientDeterminantAbs abv n q : ℂ) ^ ((t : ℂ) - ((-1 : ℝ) : ℂ))) μ := by
    have hi : Integrable (equalRankIntegrand ψ abv W W' Φ ((t + 1 : ℝ) : ℂ)) μ :=
      hconv (t + 1) (by linarith)
    rw [hfactor] at hi
    simpa only [hshift, Complex.ofReal_add, Complex.ofReal_one] using hi
  have hm := Langlands.Analysis.mellinHalfPlane (LeftUnipotentQuotient n F) μ
    (equalRankIntegrand ψ abv W W' Φ 0) (quotientDeterminantAbs abv n) (-1)
    (quotientDeterminantAbs_pos abv n) hc hd hreal
  have heq : equalRankIntegral ψ abv μ W W' Φ =
      (fun w : ℂ => ∫ q, equalRankIntegrand ψ abv W W' Φ 0 q *
        (quotientDeterminantAbs abv n q : ℂ) ^ (w - ((-1 : ℝ) : ℂ)) ∂μ) ∘
        (fun s : ℂ => s - 1) := by
    funext s
    unfold equalRankIntegral
    rw [hfactor]
    simp only [Function.comp_apply, hshift, sub_add_cancel]
  rw [heq]
  refine hm.comp (differentiableOn_id.sub_const 1) ?_
  intro s hs
  simp only [Set.mem_ofPred_eq, Complex.sub_re, Complex.one_re] at hs ⊢
  linarith

end General

/-- **Unitary generic equal-rank integrals** (Jacquet–Shalika I, Proposition (1.5)(i), with
holomorphy): absolute convergence for `Re(s) ≥ 1` and holomorphy on `Re(s) > 1`. -/
theorem unitaryEqualRankAnalytic {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
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
          IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
          IsAdmissible σ → Representation.IsIrreducible σ → IsUnitarizable σ →
          ∀ (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
            (f : (coefficientModel π ℓ).toSubmodule)
            (f' : (coefficientModel σ ℓ').toSubmodule)
            (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)),
            (∀ s : ℂ, 1 ≤ s.re →
              EqualRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) μ
                f.val f'.val Φ s) ∧
            DifferentiableOn ℂ
              (equalRankModelIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData) μ
                π σ ℓ ℓ' f f' Φ)
              {s : ℂ | 1 < s.re} := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro ψ _ μ hμ V _ _ W _ _ π σ hπa hπi hπu hσa hσi hσu ℓ ℓ' f f' Φ
  have habv : Continuous (normalizedAbsoluteValue T) :=
    NNReal.continuous_coe.comp T.continuous_normalizedAbsHom
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable
      (equalRankIntegrand ψ (normalizedAbsoluteValue T) f.val f'.val Φ s) μ := fun s =>
    (equalRankIntegrandContinuous F.Carrier n (normalizedAbsoluteValue T)
      habv V W π σ hπa.1 hσa.1 ψ ℓ ℓ' f f' Φ s).aestronglyMeasurable
  have hdet : AEMeasurable (quotientDeterminantAbs (normalizedAbsoluteValue T) n) μ :=
    (quotientDet_continuous (normalizedAbsoluteValue T) habv).measurable.aemeasurable
  have hstandard := (unitaryWeightedWhittakerSquare.{uF, uV} F n ψ μ hμ V π hπa hπi hπu).1
  have hinverse := (unitaryWeightedWhittakerSquare.{uF, uW} F n ψ μ hμ W σ hσa hσi hσu).2
  have hconv : ∀ s : ℂ, 1 ≤ s.re →
      EqualRankConverges ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ s := by
    intro s hs
    have ha : 1 / 2 ≤ s.re / 2 := by linarith
    exact equalRank_converges_of_test_weighted_squares ψ (normalizedAbsoluteValue T)
      μ f.val f'.val Φ s
      (hstandard ℓ f (sqrtNormTest Φ) (s.re / 2) ha)
      (hinverse ℓ' f' (sqrtNormTest Φ) (s.re / 2) ha)
      (hmeas s)
  refine ⟨hconv, ?_⟩
  change DifferentiableOn ℂ
    (equalRankIntegral ψ (normalizedAbsoluteValue T) μ f.val f'.val Φ)
    {s : ℂ | 1 < s.re}
  exact equalRank_holomorphic_of_real_convergence_one ψ (normalizedAbsoluteValue T) μ
    f.val f'.val Φ (hmeas 0) hdet
    (fun t ht => hconv (t : ℂ) (by simpa only [Complex.ofReal_re] using ht.le))

/-- **Jacquet–Shalika I, Proposition (1.5)(i)**: the published
`UnitaryEqualRankConvergenceStatement`, from `unitaryEqualRankAnalytic`. -/
theorem unitaryEqualRankConvergence : UnitaryEqualRankConvergenceStatement.{uF, uV, uW} := by
  intro p _ F n ψ _ μ hμ V _ _ W _ _ π σ hπg hσg hπu hσu ℓ ℓ' _ _ f f' Φ s hs
  exact (unitaryEqualRankAnalytic F n ψ μ hμ V W π σ hπg.2.1 hπg.1 hπu hσg.2.1 hσg.1 hσu
    ℓ ℓ' f f' Φ).1 s hs

end Langlands.RankinSelberg.UnitaryGeneric

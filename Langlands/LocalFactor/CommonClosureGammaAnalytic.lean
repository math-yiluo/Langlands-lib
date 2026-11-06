import Langlands.LocalFactor.CommonClosureGamma
import Langlands.LocalFactor.UnitaryGamma

/-! # Analytic representatives of the conditional common-closure gamma value -/

noncomputable section

open Filter
open scoped Topology

universe uF uV

namespace Langlands.LocalFactor.CommonClosureGammaAnalytic

open CommonClosure CommonClosureSpectral CommonClosureWeilDeligne CommonClosureGamma

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual invariant-quotient correction is entire in the spectral variable. -/
theorem quotientValue_analyticAt (E : Extension F) (A : Pair.{uF, uV} F E)
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    AnalyticAt ℂ (fun z => (quotientValue F E A Φ z : ℂ)) s := by
  have he : AnalyticAt ℂ
      (fun z : ℂ => Complex.exp (-z * (Real.log (residueCardinality F E) : ℂ))) s :=
    (analyticAt_id.neg.mul analyticAt_const).cexp
  simp_rw [quotientValue, WeilDeligne.quotientCorrectionValue_eq_eval]
  change AnalyticAt ℂ
    (fun z : ℂ => (WeilDeligne.quotientCorrectionPolynomial A (inertia F E) Φ.val).eval
      (Complex.exp (-z * (Real.log (residueCardinality F E) : ℂ)))) s
  simpa [Polynomial.aeval_def] using
    he.aeval_polynomial (WeilDeligne.quotientCorrectionPolynomial A (inertia F E) Φ.val)

/-- The full epsilon value is analytic whenever the ordinary supplied-system
value is analytic. Nonvanishing follows from its original unit-valued codomain. -/
theorem conditionalEpsilonValue_analyticAt
    (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : ℂ)
    (he : AnalyticAt ℂ
      (fun z => (conditionalDeligneValue F e ε hε E ψ μ
        (underlyingClass F E A hA) z : ℂ)) s) :
    AnalyticAt ℂ
      (fun z => (conditionalEpsilonValue F e ε hε E ψ μ A hA Φ z : ℂ)) s := by
  simp only [conditionalEpsilonValue, Units.val_mul]
  change AnalyticAt ℂ
    ((fun z => (conditionalDeligneValue F e ε hε E ψ μ
      (underlyingClass F E A hA) z : ℂ)) *
      (fun z => (quotientValue F E A Φ z : ℂ))) s
  exact he.mul (quotientValue_analyticAt F E A Φ s)

/-- The complex determinant expression using the actual conditional epsilon.
It is defined at every complex argument; its singularities are interpreted by
punctured germs. -/
def gammaExpression
    (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) : ℂ → ℂ :=
  WeilDeligne.spectralGammaExpression A (inertia F E) Φ.val
    (residueCardinality F E) (residueCardinality_pos F E)
    (fun z => (conditionalEpsilonValue F e ε hε E ψ μ A hA Φ z : ℂ))

/-- At every original common regular point this representative gives precisely
the published conditional gamma value, including the quotient correction. -/
theorem gammaExpression_eq_conditionalGammaValue
    (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : CommonClosureGamma.RegularPoint F E A Φ) :
    gammaExpression F e ε hε E ψ μ A hA Φ s.val =
      (conditionalGammaValue F e ε hε E ψ μ A hA Φ s : ℂ) := by
  rw [conditionalGammaValue, Units.val_mul, lRatioValue_eq]
  simp only [gammaExpression, WeilDeligne.spectralGammaExpression,
    operatorSpectralGamma, spectralDenominator, WeilDeligne.eulerPolynomial]
  exact mul_div_assoc _ _ _

theorem gammaExpression_meromorphicAt
    (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F E) (s : ℂ)
    (he : AnalyticAt ℂ
      (fun z => (conditionalDeligneValue F e ε hε E ψ μ
        (underlyingClass F E A hA) z : ℂ)) s) :
    MeromorphicAt (gammaExpression F e ε hε E ψ μ A hA Φ) s :=
  operatorSpectralGamma_meromorphicAt _ _ _ _ _ s
    (conditionalEpsilonValue_analyticAt F e ε hε E ψ μ A hA Φ s he)

private theorem residueCardinality_gt_one (E : Extension F) :
    1 < residueCardinality F E := by
  change (1 : ℝ) < ((fieldData F E).residueCardinality : ℝ)
  exact_mod_cast (fieldData F E).residueCardinality_gt_one

/-- Both original Euler denominators are nonzero throughout a sufficiently
small punctured neighborhood, assuming underlying unitarity. -/
theorem eventually_regular
    (E : Extension F) (A : Pair.{uF, uV} F E)
    (hU : A.toFiniteRepresentation.IsUnitary)
    (Φ : GeometricFrobenius F E) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s,
      (WeilDeligne.eulerPolynomial A (inertia F E) Φ.val).eval
        (spectralParameter (residueCardinality F E) (residueCardinality_pos F E) z : ℂ) ≠ 0 ∧
      (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A) (inertia F E) Φ.val).eval
        (spectralParameter (residueCardinality F E) (residueCardinality_pos F E)
          (1 - z) : ℂ) ≠ 0 := by
  obtain ⟨h, hh⟩ := A.isUnitary_inertiaKernelRepresentation (inertia F E) hU
  have hd := FiniteRepresentation.isUnitary_dual A.toFiniteRepresentation hU
  have hq := residueCardinality_gt_one F E
  have hfirst := spectralDenominator_eventually_ne_zero
    (WeilDeligne.kernelOperator A (inertia F E) Φ.val) h (hh Φ.val)
      (residueCardinality F E) hq s
  let R : ReciprocalEntire := {
    denominator := fun z =>
      spectralDenominator
        (WeilDeligne.kernelOperator (WeilDeligneRepresentation.dual A) (inertia F E) Φ.val)
        (residueCardinality F E) (residueCardinality_pos F E) (1 - z)
    entire := fun z =>
      ((analyticAt_spectralDenominator _ _ _ (1 - z)).comp
        (analyticAt_const.sub analyticAt_id)).differentiableAt
    nonzero := ⟨0, by
      simpa only [sub_zero, spectralDenominator, WeilDeligne.eulerPolynomial] using
        WeilDeligne.eulerPolynomial_spectral_eval_ne_zero_of_isUnitary
          (WeilDeligneRepresentation.dual A) (inertia F E) hd Φ.val
            (q := residueCardinality F E) hq (s := 1) (by simp)⟩ }
  exact hfirst.and (R.denominator_eventually_ne_zero s)

/-- Every complex function agreeing with conditional gamma at all original
regular points has the same punctured germ as the determinant expression. -/
theorem eventuallyEq_gammaExpression
    (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (hU : A.toFiniteRepresentation.IsUnitary) (Φ : GeometricFrobenius F E)
    (g : ℂ → ℂ)
    (hg : ∀ z : CommonClosureGamma.RegularPoint F E A Φ,
      g z.val = (conditionalGammaValue F e ε hε E ψ μ A hA Φ z : ℂ))
    (s : ℂ) :
    g =ᶠ[𝓝[≠] s] gammaExpression F e ε hε E ψ μ A hA Φ := by
  filter_upwards [eventually_regular F E A hU Φ s] with z hz
  exact (hg ⟨z, hz⟩).trans
    (gammaExpression_eq_conditionalGammaValue F e ε hε E ψ μ A hA Φ ⟨z, hz⟩).symm

/-- For any representative agreeing on the original regular domain, the
unitary real-zero restriction transfers through equality of punctured germs.
Only ordinary epsilon analyticity remains an explicit analytic premise. -/
theorem real_positive_order_only_zero
    (e : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uV} F)
    (hε : NonabelianSystem.IsSystem F e ε) (E : Extension F)
    (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E)
    (A : Pair.{uF, uV} F E) (hA : A.toFiniteRepresentation.IsContinuous)
    (hU : A.toFiniteRepresentation.IsUnitary) (Φ : GeometricFrobenius F E)
    (he : ∀ t : ℝ, AnalyticAt ℂ
      (fun z => (conditionalDeligneValue F e ε hε E ψ μ
        (underlyingClass F E A hA) z : ℂ)) (t : ℂ))
    (g : ℂ → ℂ)
    (hg : ∀ z : CommonClosureGamma.RegularPoint F E A Φ,
      g z.val = (conditionalGammaValue F e ε hε E ψ μ A hA Φ z : ℂ))
    (t : ℝ) (ht : 0 < meromorphicOrderAt g (t : ℂ)) :
    t = 0 := by
  rw [meromorphicOrderAt_congr
    (eventuallyEq_gammaExpression F e ε hε E ψ μ A hA hU Φ g hg t)] at ht
  exact WeilDeligne.spectralGammaExpression_real_positive_order_only_zero
    A (inertia F E) hU Φ.val (residueCardinality F E) (residueCardinality_gt_one F E)
    (fun z => (conditionalEpsilonValue F e ε hε E ψ μ A hA Φ z : ℂ))
    (fun x => ⟨conditionalEpsilonValue_analyticAt F e ε hε E ψ μ A hA Φ x (he x),
      Units.ne_zero _⟩) t ht

end Langlands.LocalFactor.CommonClosureGammaAnalytic

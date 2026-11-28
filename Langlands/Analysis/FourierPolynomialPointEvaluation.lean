import Langlands.Analysis.SchwartzPolynomialFourierTest
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-! # Polynomial point distributions and their Fourier phases -/

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform LineDeriv SchwartzMap Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The normalized monomial differential evaluation on a spectral test. -/
def fourierPolynomialPointEvaluation {n : ℕ} (m : Fin n → V) (ξ : V) (a : V → ℂ) : ℂ :=
  (-(2 * (Real.pi : ℂ) * Complex.I))⁻¹ ^ n * iteratedFDeriv ℝ n a ξ m

private theorem iteratedFDeriv_negativePhase {n : ℕ} (m : Fin n → V) (ξ x : V) :
    iteratedFDeriv ℝ n (fun z => Complex.exp (((-2 * Real.pi * inner ℝ x z : ℝ) : ℂ) * Complex.I)) ξ m =
      (-(2 * (Real.pi : ℂ) * Complex.I)) ^ n * (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) *
        Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) := by
  let w := (-2 * Real.pi) • x
  have hchar : (fun z => Complex.exp (((-2 * Real.pi * inner ℝ x z : ℝ) : ℂ) * Complex.I)) =
      charFun (Measure.dirac w) := by
    funext z
    simp only [charFun_dirac, w, real_inner_smul_left]
  have hm : MemLp id (n : ENNReal) (Measure.dirac w) := memLp_dirac (by finiteness)
  rw [hchar, iteratedFDeriv_charFun hm, integral_dirac]
  simp only [w, real_inner_smul_left, Complex.ofReal_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) = Complex.I * (-2 * (Real.pi : ℂ)) by ring, mul_pow]
  ring

/-- The differential evaluation is local at the frequency. Its Schwartz value is the
whole-space polynomial Fourier test, and its value on a negative phase is the spatial
monomial times that phase at the frequency. -/
def FourierPolynomialPointEvaluationStatement : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {n : ℕ} (m : Fin n → V) (ξ : V),
    let L := fourierPolynomialPointEvaluation m ξ
    (∀ a b, a =ᶠ[𝓝 ξ] b → L a = L b) ∧
    (∀ a : 𝓢(V, ℂ),
      let g (x : V) := Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
        (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) * (𝓕⁻ a) x
      Integrable g ∧ (∫ x, g x) = L a) ∧
    ∀ x : V,
      L (fun z => Complex.exp (((-2 * Real.pi * inner ℝ x z : ℝ) : ℂ) * Complex.I)) =
        (∏ i, ((inner ℝ x (m i) : ℝ) : ℂ)) *
          Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I)

theorem fourierPolynomialPointEvaluation_spec : FourierPolynomialPointEvaluationStatement := by
  intro V _ _ _ _ _ n m ξ L
  refine ⟨?_, ?_, ?_⟩
  · intro a b h
    unfold L fourierPolynomialPointEvaluation
    rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]
  · intro a
    simpa only [L, fourierPolynomialPointEvaluation, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
      using schwartzPolynomialFourierTest m a ξ
  · intro x
    unfold L fourierPolynomialPointEvaluation
    rw [iteratedFDeriv_negativePhase]
    have h : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      exact neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_mul]

end Langlands.Analysis

import Langlands.Global.AdelicRegularizedConeFourierBoundary
import Langlands.Global.AdelicInducedInnerProduct
import Langlands.Analysis.FourierPolynomialPointEvaluation

/-! # Normalized Fourier evaluation in coroot coordinates -/

noncomputable section

open Filter MeasureTheory
open scoped Classical ContDiff ENNReal FourierTransform InnerProductSpace Topology

set_option autoImplicit false

namespace Langlands.Global

open AdelicGroupPoints Langlands.Analysis

variable {ι : Type*} [Fintype ι]

local notation "τ" => (2 * Real.pi)
local notation "V" => EuclideanSpace ℝ ι

private theorem twoPi_pos : 0 < τ := mul_pos (by norm_num) Real.pi_pos

/-- The spectral Lebesgue measure paired with spatial product Lebesgue measure for
an exponential with phase `-i ∑ i, x i * z i`. -/
def coordinateSpectralMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  (ENNReal.ofReal τ)⁻¹ ^ Fintype.card ι • volume

@[simp]
theorem coordinateSpectralMeasure_fin (n : ℕ) :
    coordinateSpectralMeasure (Fin n) = spectralMeasure n := by
  rw [coordinateSpectralMeasure, spectralMeasure, Fintype.card_fin]

/-- The negative Fourier phase in real coordinates without the factor `2π`. -/
def coordinateFourierPhase (x z : ι → ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-(∑ i, x i * z i) : ℝ) : ℂ))

theorem contDiff_coordinateFourierPhase (x : ι → ℝ) :
    ContDiff ℝ ∞ (coordinateFourierPhase x) := by
  have h : ContDiff ℝ ∞ (fun z : ι → ℝ => -(∑ i, x i * z i)) := by fun_prop
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h))

private def euclideanCoordinates : V ≃L[ℝ] (ι → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)

private theorem inner_coordinates (x z : V) : ⟪x, z⟫_ℝ = ∑ i, x i * z i := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

private theorem coordinateFourierPhase_euclidean (x : V) (z : ι → ℝ) :
    coordinateFourierPhase (euclideanCoordinates (τ • x)) z =
      Complex.exp (((-2 * Real.pi * ⟪x, WithLp.toLp 2 z⟫_ℝ : ℝ) : ℂ) * Complex.I) := by
  rw [coordinateFourierPhase, inner_coordinates, mul_comm Complex.I]
  congr 2
  simp only [euclideanCoordinates, PiLp.continuousLinearEquiv_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, neg_mul, Finset.mul_sum, Finset.sum_neg_distrib]
  exact congrArg (fun r : ℝ => ((-r : ℝ) : ℂ)) (Finset.sum_congr rfl fun i _ => by ring)

private def coefficientSchwartz (a : (ι → ℝ) → ℂ) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) : SchwartzMap V ℂ :=
  (hc.comp_homeomorph (euclideanCoordinates (ι := ι)).toHomeomorph).toSchwartzMap
    (ha.comp (euclideanCoordinates (ι := ι)).contDiff)

private theorem orthantFourierTest_translate (a : (ι → ℝ) → ℂ) (ξ x : ι → ℝ) :
    orthantFourierTest (coordinateSpectralMeasure ι) (fun z => a (z + ξ)) x =
      coordinateFourierPhase (-x) ξ * orthantFourierTest (coordinateSpectralMeasure ι) a x := by
  let f (z : ι → ℝ) := coordinateFourierPhase x z * a z
  have hphase (z : ι → ℝ) : coordinateFourierPhase (-x) ξ * coordinateFourierPhase x (z + ξ) =
      coordinateFourierPhase x z := by
    simp only [coordinateFourierPhase, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib,
      neg_neg, Pi.add_apply, mul_add, Finset.sum_add_distrib, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  change (∫ z, coordinateFourierPhase x z * a (z + ξ) ∂coordinateSpectralMeasure ι) =
    coordinateFourierPhase (-x) ξ * ∫ z, f z ∂coordinateSpectralMeasure ι
  simp only [coordinateSpectralMeasure, integral_smul_measure]
  rw [mul_smul_comm, ← integral_add_right_eq_self f ξ, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => by simp only [f, ← mul_assoc, hphase]

private theorem orthantFourierTest_neg_scaled (a : (ι → ℝ) → ℂ) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) (x : V) :
    orthantFourierTest (coordinateSpectralMeasure ι) a (euclideanCoordinates ((-τ) • x)) =
      τ⁻¹ ^ Fintype.card ι • (𝓕⁻ (coefficientSchwartz a ha hc)) x := by
  rw [orthantFourierTest, coordinateSpectralMeasure, integral_smul_measure, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal twoPi_pos.le, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  rw [← (PiLp.volume_preserving_ofLp ι).integral_comp
    (euclideanCoordinates (ι := ι)).toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    change coordinateFourierPhase (euclideanCoordinates ((-τ) • x)) z.ofLp * a z.ofLp = _
    rw [neg_smul, ← smul_neg, coordinateFourierPhase_euclidean]
    simp [coefficientSchwartz, euclideanCoordinates, real_inner_comm, smul_eq_mul]
    rfl

private def monomialDirections (k : ι →₀ ℕ) :
    Fin (Fintype.card (Σ i, Fin (k i))) → V :=
  fun j => EuclideanSpace.single ((Fintype.equivFin (Σ i, Fin (k i))).symm j).1 1

private theorem prod_monomialDirections (k : ι →₀ ℕ) (x : V) :
    (∏ j, ((⟪x, monomialDirections k j⟫_ℝ : ℝ) : ℂ)) = ∏ i, (x i : ℂ) ^ k i := by
  calc
    _ = ∏ j : (Σ i, Fin (k i)), (x j.1 : ℂ) := by
      refine Fintype.prod_equiv (Fintype.equivFin (Σ i, Fin (k i))).symm _ _ fun j => ?_
      simp [monomialDirections, EuclideanSpace.inner_single_right]
    _ = ∏ i, ∏ _ : Fin (k i), (x i : ℂ) :=
      Fintype.prod_sigma' (fun i (_ : Fin (k i)) => (x i : ℂ))
    _ = _ := by simp

/-- The finite sum of the transposed monomial derivatives of the test at `ξ`.
The powers of `2π` convert the Euclidean Fourier convention to the coordinate phase. -/
def coordinatePolynomialPointEvaluation (P : MvPolynomial ι ℂ) (ξ : ι → ℝ)
    (a : (ι → ℝ) → ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * (τ : ℂ) ^ Fintype.card (Σ i, Fin (k i)) *
    fourierPolynomialPointEvaluation (monomialDirections k) (WithLp.toLp 2 ξ)
      (a ∘ (euclideanCoordinates (ι := ι)))

private theorem eval_scaled_polynomial (P : MvPolynomial ι ℂ) (x : V) :
    MvPolynomial.eval (fun i => ((τ * x i : ℝ) : ℂ)) P =
      ∑ k ∈ P.support, (P.coeff k * (τ : ℂ) ^ Fintype.card (Σ i, Fin (k i))) *
        ∏ j, ((⟪x, monomialDirections k j⟫_ℝ : ℝ) : ℂ) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_pow, Finset.prod_mul_distrib,
    ← Finset.prod_pow_eq_pow_sum, Fintype.card_sigma, Fintype.card_fin, prod_monomialDirections,
    mul_assoc]

/-- Testing a reflected polynomial on the whole coordinate space gives the local
point distribution at the spectral shift. On a negative Fourier phase the distribution
returns the original polynomial at the spatial point times that phase. -/
def CoordinatePolynomialFourierEvaluationStatement : Prop :=
  ∀ {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) (ξ : ι → ℝ),
    let L := coordinatePolynomialPointEvaluation P ξ
    (∀ a b, a =ᶠ[𝓝 ξ] b → L a = L b) ∧
    (∀ a : (ι → ℝ) → ℂ, ContDiff ℝ ∞ a → HasCompactSupport a →
      let f := orthantPolynomialTest (coordinateSpectralMeasure ι) (fun z => a (z + ξ)) P
      Integrable f ∧ (∫ x, f x) = L a) ∧
    ∀ x : ι → ℝ, L (coordinateFourierPhase x) =
      MvPolynomial.eval (fun i => (x i : ℂ)) P * coordinateFourierPhase x ξ

theorem coordinatePolynomialFourierEvaluation : CoordinatePolynomialFourierEvaluationStatement := by
  intro ι _ P ξ L
  classical
  let q := euclideanCoordinates (ι := ι)
  let w : EuclideanSpace ℝ ι := WithLp.toLp 2 ξ
  have hq : MeasurePreserving q volume volume := PiLp.volume_preserving_ofLp ι
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have h := q.continuous.continuousAt (x := w) |>.tendsto
    change Tendsto q (𝓝 w) (𝓝 ξ) at h
    have he : a ∘ q =ᶠ[𝓝 w] b ∘ q := h.eventually hab
    unfold L coordinatePolynomialPointEvaluation
    exact Finset.sum_congr rfl fun k _ => congrArg (_ * ·)
      ((fourierPolynomialPointEvaluation_spec (monomialDirections k) w).1 _ _ he)
  · intro a ha hc
    dsimp only
    let B := coefficientSchwartz a ha hc
    let phase (x : EuclideanSpace ℝ ι) :=
      Complex.exp (((-2 * Real.pi * ⟪x, w⟫_ℝ : ℝ) : ℂ) * Complex.I)
    let g (k : ι →₀ ℕ) (x : EuclideanSpace ℝ ι) := phase x *
      (∏ j, ((⟪x, monomialDirections k j⟫_ℝ : ℝ) : ℂ)) * (𝓕⁻ B) x
    let c (k : ι →₀ ℕ) := P.coeff k * (τ : ℂ) ^ Fintype.card (Σ i, Fin (k i))
    let G (x : EuclideanSpace ℝ ι) := ∑ k ∈ P.support, c k * g k x
    let f := orthantPolynomialTest (coordinateSpectralMeasure ι) (fun z => a (z + ξ)) P
    have hg (k : ι →₀ ℕ) := (fourierPolynomialPointEvaluation_spec (monomialDirections k) w).2.1 B
    have hG : Integrable G := integrable_finsetSum _ fun k _ => (hg k).1.const_mul _
    have hfun (x : EuclideanSpace ℝ ι) :
        f (q ((-τ) • x)) = τ⁻¹ ^ Fintype.card ι • G x := by
      dsimp only [f, orthantPolynomialTest]
      change _ * orthantFourierTest (coordinateSpectralMeasure ι) (fun z => a (z + ξ))
        (euclideanCoordinates ((-τ) • x)) = _
      rw [orthantFourierTest_translate, orthantFourierTest_neg_scaled _ ha hc,
        show -q ((-τ) • x) = q (τ • x) by rw [neg_smul, map_neg, neg_neg]]
      change _ * (coordinateFourierPhase (euclideanCoordinates (τ • x)) ξ * _) = _
      rw [coordinateFourierPhase_euclidean]
      have hx (i : ι) : -(q ((-τ) • x) i : ℂ) = ((τ * x i : ℝ) : ℂ) := by
        simp [q, euclideanCoordinates]
      simp only [hx, eval_scaled_polynomial, G, g, c, phase, B, Complex.real_smul]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hInt : Integrable (fun x : EuclideanSpace ℝ ι => f (q ((-τ) • x))) := by
      have hG' : Integrable (fun x => τ⁻¹ ^ Fintype.card ι • G x) :=
        hG.smul (τ⁻¹ ^ Fintype.card ι)
      simpa only [hfun] using hG'
    have hτ : -τ ≠ 0 := neg_ne_zero.mpr twoPi_pos.ne'
    refine ⟨(hq.integrable_comp_emb q.toHomeomorph.measurableEmbedding).mp
      ((integrable_comp_smul_iff volume (fun x : EuclideanSpace ℝ ι => f (q x)) hτ).mp hInt), ?_⟩
    change (∫ x, f x) = L a
    rw [← hq.integral_comp q.toHomeomorph.measurableEmbedding f]
    calc
      (∫ x : EuclideanSpace ℝ ι, f (q x)) =
        ∫ x : EuclideanSpace ℝ ι, f (q ((-τ) • ((-τ)⁻¹ • x))) := by
        simp_rw [smul_smul, mul_inv_cancel₀ hτ, one_smul]
      _ = |(-τ) ^ Module.finrank ℝ (EuclideanSpace ℝ ι)| •
          ∫ x : EuclideanSpace ℝ ι, f (q ((-τ) • x)) :=
        Measure.integral_comp_inv_smul volume (fun x : EuclideanSpace ℝ ι => f (q ((-τ) • x))) (-τ)
      _ = L a := by
        simp only [hfun, finrank_euclideanSpace, abs_pow, abs_neg, abs_of_pos twoPi_pos]
        rw [integral_smul (μ := volume) (τ⁻¹ ^ Fintype.card ι) G, smul_smul, ← mul_pow,
          mul_inv_cancel₀ twoPi_pos.ne', one_pow, one_smul]
        unfold G L coordinatePolynomialPointEvaluation
        rw [integral_finsetSum _ (fun k _ => (hg k).1.const_mul _)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, (hg k).2]
        rfl
  · intro x
    let y : EuclideanSpace ℝ ι := τ⁻¹ • WithLp.toLp 2 x
    have hy : q (τ • y) = x := by
      dsimp only [y]
      rw [smul_smul, mul_inv_cancel₀ twoPi_pos.ne', one_smul]
      rfl
    have hp (z : EuclideanSpace ℝ ι) : coordinateFourierPhase x (q z) =
        Complex.exp (((-2 * Real.pi * ⟪y, z⟫_ℝ : ℝ) : ℂ) * Complex.I) := by
      rw [← hy, coordinateFourierPhase_euclidean]
      rfl
    have he := eval_scaled_polynomial P y
    have hxy (i : ι) : τ * y i = x i := by
      exact congrFun hy i
    rw [show MvPolynomial.eval (fun i => (x i : ℂ)) P = _ from by
      simpa only [hxy] using he, Finset.sum_mul]
    unfold L coordinatePolynomialPointEvaluation
    refine Finset.sum_congr rfl fun k _ => ?_
    have harg : coordinateFourierPhase x ∘ q =
        fun z => Complex.exp (((-2 * Real.pi * ⟪y, z⟫_ℝ : ℝ) : ℂ) * Complex.I) := funext hp
    change _ * fourierPolynomialPointEvaluation (monomialDirections k) w (coordinateFourierPhase x ∘ q) = _
    rw [harg, (fourierPolynomialPointEvaluation_spec (monomialDirections k) w).2.2 y, ← hp w]
    simp only [mul_assoc, show q w = ξ from rfl]

end Langlands.Global

import Langlands.Global.Factors.HeckeThetaBridges
import Langlands.Global.Hecke.ThetaUnfolding
import Langlands.Global.Hecke.MixedCharacter

/-! # The dual Mellin identity of the Fourier theta series of a divisor -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Topology NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors Classical

namespace Langlands.Global.HeckeTheta

open Langlands.LocalFactor.PadicAbelian Langlands.Global.CompletionPadic
open Langlands.ClassField.Global Langlands.Global.HeckeDivisor
open Langlands.Global.HeckeDivisorEulerProduct
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation

universe u

variable {K : Type u} [Field K] [NumberField K]

section Dual

variable
    (χ : HeckeCharacter K)
    (ψf : ∀ v : FinitePlace K,
      @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
        (topologicalData v).topology)
    (μ : ∀ v : FinitePlace K, SelfDualHaar (topologicalData v) (ψf v))
    (Sψ : Finset (FinitePlace K))
    (hψ : ∀ v ∉ Sψ, (topologicalData v).additiveConductor (ψf v) = 0)
    (dR dR' : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (hR' : ∀ v, IsRealCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dR' v))
    (dC dC' : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))
    (hC' : ∀ v, IsComplexCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dC' v))

include hψ hR hC in
/-- At the inverse `γ⁻¹` of a nonzero field element, the Fourier theta coefficient divided by
the mixed character at `γ` and multiplied by `N(γ)^s` is the Fourier divisor Euler
coefficient at `-principalDivisor γ - d` times the dual class factor. -/
theorem fourierThetaCoeff_inv_mul_eq_coefficient (d : FinitePlaceDivisor K) (γ : Kˣ) (s : ℂ)
    (S : Finset (FinitePlace K)) (hS : ∀ v ∉ S, fourierShellWeight χ ψf μ v s 0 = 1) :
    fourierThetaCoeff χ ψf μ d ((γ⁻¹ : Kˣ) : K) *
        (Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
          (fun v => (dC v).weight) (fun v => (dC v).exponent) (mixedEmbedding K (γ : K)))⁻¹ *
        ((mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℝ) : ℂ) ^ s =
      DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s)
          (-principalDivisor γ - d) * dualClassFactor χ d s := by
  have h := fourierThetaCoeff_mul_eq_coefficient χ ψf μ Sψ hψ dR hR dC hC d γ⁻¹ s S hS
  rw [principalDivisor_inv] at h
  set χV := Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
    (fun v => (dC v).weight) (fun v => (dC v).exponent) with hχV
  have hx := Hecke.norm_mixedEmbedding_units_ne_zero γ
  have hpos := Hecke.norm_mixedEmbedding_units_pos γ
  have hinv : mixedEmbedding K ((γ⁻¹ : Kˣ) : K) = (mixedEmbedding K (γ : K))⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Hecke.mixedEmbedding_inv]
  have hχinv : χV (mixedEmbedding K ((γ⁻¹ : Kˣ) : K)) = (χV (mixedEmbedding K (γ : K)))⁻¹ := by
    rw [hinv]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [hχV, ← Hecke.mixedCharFun_mul, Hecke.mul_inv_cancel_of_norm_ne_zero hx,
      Hecke.mixedCharFun_one]
  have hN : ((mixedEmbedding.norm (mixedEmbedding K ((γ⁻¹ : Kˣ) : K)) : ℝ) : ℂ) ^ (-s) =
      ((mixedEmbedding.norm (mixedEmbedding K (γ : K)) : ℝ) : ℂ) ^ s := by
    rw [hinv, Hecke.norm_inv', Hecke.ofReal_inv_cpow_of_nonneg hpos.le, neg_neg]
  rw [← h, hχinv, hN]

/-- The dual principal series of a divisor `d`: the sum over the principal divisors `p` of
the Fourier divisor Euler coefficients at `-p - d`, that is, over the divisor class of
`-d`. -/
def dualPrincipalSeries (S : Finset (FinitePlace K)) (d : FinitePlaceDivisor K) (s : ℂ) : ℂ :=
  ∑' p : principalDivisors K, DivisorEulerProduct.coefficient S
    (fun v => fourierShellWeight χ ψf μ v s) (-(p : FinitePlaceDivisor K) - d)

/-- If the Fourier divisor Euler coefficients are absolutely summable, their restriction to
the divisors `-p - d` with `p` principal sums to the dual principal series. -/
theorem hasSum_dualPrincipalSeries (S : Finset (FinitePlace K)) (d : FinitePlaceDivisor K)
    (s : ℂ) (hcoef : Summable fun D =>
      ‖DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) D‖) :
    HasSum (fun p : principalDivisors K => DivisorEulerProduct.coefficient S
        (fun v => fourierShellWeight χ ψf μ v s) (-(p : FinitePlaceDivisor K) - d))
      (dualPrincipalSeries χ ψf μ S d s) := by
  have hinj : Function.Injective fun p : principalDivisors K =>
      -(p : FinitePlaceDivisor K) - d :=
    fun p q h => Subtype.ext (neg_injective (sub_left_injective h))
  exact (hcoef.comp_injective hinj).of_norm.hasSum

include hψ hR hR' hC hC' in
/-- **The dual per-divisor Mellin identity.** Let `G` have Gaussian decay, let `S` contain the
places where the zeroth Fourier shell weight is not one, let the Fourier divisor Euler
coefficients be absolutely summable and let `G χ_∞' N^(s-1)` be integrable, where `χ_∞` and
`χ_∞'` are the mixed characters of the presentations of `χ` and `χ⁻¹`. Then
`classFactor(d, 1 - s) ∫_C (θ(b_d, G)(x⁻¹) - b_d(0) G(0)) χ_∞(x) N(x)^(-s-1) dx
  = w (∫_V G χ_∞' N^(s-1)) ∑_{p principal} c_s(-p - d)`,
where `b_d` is the Fourier theta coefficient of `d` and `c_s` the Fourier divisor Euler
coefficient. -/
theorem classFactor_one_sub_mul_integral_fourierTheta (d : FinitePlaceDivisor K)
    {G : mixedSpace K → ℂ} {C c : ℝ} (hc : 0 < c)
    (hG : ∀ z, ‖G z‖ ≤ C * Real.exp (-(c * ‖z‖ ^ 2))) (s : ℂ) (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, fourierShellWeight χ ψf μ v s 0 = 1)
    (hcoef : Summable fun D =>
      ‖DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s) D‖)
    (hint : Integrable fun y => G y *
      Hecke.mixedCharFun (fun v => (dR' v).parity) (fun v => (dR' v).exponent)
        (fun v => (dC' v).weight) (fun v => (dC' v).exponent) y *
      ((mixedEmbedding.norm y : ℝ) : ℂ) ^ (s - 1)) :
    classFactor χ d (1 - s) *
        ∫ x in fundamentalCone K,
          (Hecke.thetaSeries (fourierThetaCoeff χ ψf μ d) G x⁻¹ -
              fourierThetaCoeff χ ψf μ d 0 * G 0) *
            Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
              (fun v => (dC v).weight) (fun v => (dC v).exponent) x *
            ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (-s - 1) =
      (Units.torsionOrder K : ℂ) *
        (∫ y, G y *
          Hecke.mixedCharFun (fun v => (dR' v).parity) (fun v => (dR' v).exponent)
            (fun v => (dC' v).weight) (fun v => (dC' v).exponent) y *
          ((mixedEmbedding.norm y : ℝ) : ℂ) ^ (s - 1)) *
        ∑' p : principalDivisors K, DivisorEulerProduct.coefficient S
          (fun v => fourierShellWeight χ ψf μ v s) (-(p : FinitePlaceDivisor K) - d) := by
  set χV := Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
    (fun v => (dC v).weight) (fun v => (dC v).exponent) with hχV
  set χV' := Hecke.mixedCharFun (fun v => (dR' v).parity) (fun v => (dR' v).exponent)
    (fun v => (dC' v).weight) (fun v => (dC' v).exponent) with hχV'
  have hdual : ∀ y, χV' y = χV y⁻¹ := fun y =>
    mixedCharFun_dual_eq_inv_apply χ dR dR' hR hR' dC dC' hC hC' y
  -- the archimedean integral after inversion
  obtain ⟨hInt, hEq⟩ := Hecke.integral_inv_eq_and_integrable G χV s
  have hint' : Integrable fun y =>
      G y⁻¹ * χV y * ((mixedEmbedding.norm y : ℝ) : ℂ) ^ (-s - 1) := by
    refine hInt.mpr (hint.congr (Eventually.of_forall fun y => ?_))
    simp only [hdual]
  have hI : ∫ y, G y⁻¹ * χV y * ((mixedEmbedding.norm y : ℝ) : ℂ) ^ (-s - 1) =
      ∫ y, G y * χV' y * ((mixedEmbedding.norm y : ℝ) : ℂ) ^ (s - 1) := by
    rw [hEq]
    simp only [hdual]
  -- the coefficient data
  obtain ⟨e, -, hsupp⟩ := exists_fourierThetaCoeff_support χ ψf μ Sψ hψ d
  obtain ⟨M, hM⟩ := exists_norm_fourierThetaCoeff_le χ ψf μ Sψ hψ d
  have hterm : ∀ p : principalDivisors K,
      fourierThetaCoeff χ ψf μ d (((principalGenerator p)⁻¹ : Kˣ) : K) *
          (χV (mixedEmbedding K (principalGenerator p : K)))⁻¹ *
          ((mixedEmbedding.norm (mixedEmbedding K (principalGenerator p : K)) : ℝ) : ℂ) ^ s =
        DivisorEulerProduct.coefficient S (fun v => fourierShellWeight χ ψf μ v s)
          (-(p : FinitePlaceDivisor K) - d) * dualClassFactor χ d s := fun p => by
    rw [fourierThetaCoeff_inv_mul_eq_coefficient χ ψf μ Sψ hψ dR hR dC hC d _ s S hS,
      principalDivisor_principalGenerator]
  have hinj : Function.Injective fun p : principalDivisors K =>
      -(p : FinitePlaceDivisor K) - d :=
    fun p q h => Subtype.ext (neg_injective (sub_left_injective h))
  have hsum : Summable fun p : principalDivisors K =>
      ‖fourierThetaCoeff χ ψf μ d (((principalGenerator p)⁻¹ : Kˣ) : K)‖ *
        ‖χV (mixedEmbedding K (principalGenerator p : K))‖⁻¹ *
        mixedEmbedding.norm (mixedEmbedding K (principalGenerator p : K)) ^ s.re := by
    refine ((hcoef.comp_injective hinj).mul_right ‖dualClassFactor χ d s‖).congr fun p => ?_
    have h := congrArg Norm.norm (hterm p)
    simp only [norm_mul, norm_inv] at h
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Hecke.norm_mixedEmbedding_units_pos _)] at h
    exact h.symm
  -- unfolding
  have hunfold := Hecke.integral_thetaSeries_inv_unfold (χ := χV)
    (fun x y _ _ => Hecke.mixedCharFun_mul _ _ _ _ x y) (Hecke.mixedCharFun_one _ _ _ _)
    principalGenerator principalUnitsEquiv (fun p u => rfl) (Hecke.latticeIdeal e) hsupp hM
    (fourierThetaCoeff_unit_mul χ ψf μ Sψ hψ dR hR dC hC d) hc hG s hsum hint'
  rw [hunfold, hI]
  simp only [hterm]
  rw [tsum_mul_right, tsum_mul_right]
  linear_combination ((Units.torsionOrder K : ℂ) *
    (∫ y, G y * χV' y * ((mixedEmbedding.norm y : ℝ) : ℂ) ^ (s - 1)) *
    ∑' p : principalDivisors K, DivisorEulerProduct.coefficient S
      (fun v => fourierShellWeight χ ψf μ v s) (-(p : FinitePlaceDivisor K) - d)) *
    classFactor_one_sub_mul_dualClassFactor χ d s

end Dual

end Langlands.Global.HeckeTheta

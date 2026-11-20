import Langlands.Representation.GodementJacquet.ComplexDiagonalTateIdentity
import Langlands.Global.RankinSelberg.ArchimedeanSchwartzTensor
import Langlands.LocalFactor.Archimedean.Statement

/-! # The normalized product Tate equation on the common strip -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor

variable {ι : Type*} [Fintype ι]
local notation "Z" => ι → ℂ

omit [Fintype ι] in
private theorem traceCharacter_sum (a : ℂˣ) (s : Finset ι) (x : Z) :
    traceCharacter a (∑ i ∈ s, x i) = ∏ i ∈ s, traceCharacter a (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, traceCharacter_add, ih]

/-- The Fourier transform of an external product is the external product of
the scalar trace transforms. -/
theorem complexCoordinateFourier_finiteTensor (a : ℂˣ)
    (f : ι → SchwartzMap ℂ ℂ) (z : Z) :
    complexCoordinateFourier a (finiteTensor f) z = ∏ i, complexScalarFourier a (f i) (z i) := by
  let : (complexSelfDualMeasure a).measure.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  unfold complexCoordinateFourier complexCoordinatePair complexCoordinateMeasure
  simp only [traceCharacter_sum, finiteTensor_apply, ← Finset.prod_mul_distrib, complexScalarFourier]
  exact integral_fintype_prod_eq_prod (fun i x => f i x * traceCharacter a (x * z i))

/-- Initial diagonal zeta integration factors on external products. -/
theorem complexDiagonalZeta_finiteTensor (a : ℂˣ) (f : ι → SchwartzMap ℂ ℂ)
    (m : ι → ℤ) {u : Z} (hu : ∀ i, 0 < (u i).re) :
    complexDiagonalZeta a (finiteTensor f) m u =
      ∏ i, ∫ z, f i z * complexMellinWeight (m i) (u i) z ∂(complexSelfDualMeasure a).measure := by
  let : (complexSelfDualMeasure a).measure.IsAddHaarMeasure := (complexSelfDualMeasure a).isAddHaar
  rw [complexDiagonalZeta_eq_integral _ _ _ hu]
  simp only [complexDiagonalZetaKernel, finiteTensor_apply, ← Finset.prod_mul_distrib,
    complexCoordinateMeasure]
  exact integral_fintype_prod_eq_prod (fun i z => f i z * complexMellinWeight (m i) (u i) z)

private theorem complexSelfDualMeasure_one :
    (complexSelfDualMeasure (1 : ℂˣ)).measure = (2 : ℝ≥0∞) • (volume : Measure ℂ) := by
  rw [complexSelfDualMeasure, complexScaledMeasure_measure]
  change ((↑(‖(↑(1 : ℂˣ) : ℂ)‖₊ * 2) : ENNReal) • (volume : Measure ℂ)) = _
  simp

private theorem traceCharacter_one_exp (z : ℂ) :
    traceCharacter 1 z = Complex.exp (4 * (Real.pi : ℂ) * Complex.I * (z.re : ℂ)) := by
  change (((Real.fourierChar (Algebra.trace ℝ ℂ ((↑(1 : ℂˣ) : ℂ) * z))) : Circle) : ℂ) = _
  rw [Real.fourierChar_apply, Units.val_one, one_mul, Algebra.trace_complex_apply]
  congr 1
  push_cast
  ring

private def tateGaussian (m : ℤ) (z : ℂ) : ℂ :=
  (if 0 ≤ m then starRingEnd ℂ z ^ m.natAbs else z ^ m.natAbs) *
    Complex.exp (-2 * (Real.pi : ℂ) * (‖z‖ : ℂ) ^ 2) / (Real.pi : ℂ)

private theorem exists_schwartz_tateGaussian (hTate : ComplexArchimedeanTateStatement) (m : ℤ) :
    ∃ f : SchwartzMap ℂ ℂ, (f : ℂ → ℂ) = tateGaussian m := by
  obtain ⟨_, _, _, h⟩ := hTate
  obtain ⟨f, hf⟩ := (h m).1
  exact ⟨f, funext hf⟩

private theorem complexScalarFourier_tateGaussian (hTate : ComplexArchimedeanTateStatement)
    (m : ℤ) (z : ℂ) :
    complexScalarFourier 1 (tateGaussian m) z = Complex.I ^ m.natAbs * tateGaussian (-m) z := by
  obtain ⟨_, _, _, hg⟩ := hTate
  have h := (hg m).2.1 z
  rw [complexScalarFourier, complexSelfDualMeasure_one]
  simp only [traceCharacter_one_exp, tateGaussian]
  simpa only [NNReal.coe_one, Complex.ofReal_one, one_mul, mul_one, mul_comm] using h

private theorem integral_tateGaussian (hTate : ComplexArchimedeanTateStatement)
    (m : ℤ) {u : ℂ} (hu : 0 < u.re) :
    (∫ z, tateGaussian m z * complexMellinWeight m u z
       ∂(complexSelfDualMeasure (1 : ℂˣ)).measure) =
      Complex.Gammaℂ (u + (m.natAbs : ℂ) / 2) := by
  obtain ⟨_, _, _, hg⟩ := hTate
  have h := (hg m).2.2 0 u (by simpa only [add_zero] using hu)
  simp only [add_zero] at h
  rw [complexSelfDualMeasure_one, ← h]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [tateGaussian, complexMellinWeight]
  split_ifs <;> ring

/-- The product of the scalar complex Gamma factors. -/
def complexDiagonalGamma (m : ι → ℤ) (u : Z) : ℂ :=
  ∏ i, Complex.Gammaℂ (u i + ((m i).natAbs : ℂ) / 2)

/-- The product of the scalar epsilon factors for the basic trace character. -/
def complexDiagonalStandardEpsilon (m : ι → ℤ) : ℂ :=
  ∏ i, Complex.I ^ (m i).natAbs

private theorem complexDiagonalGamma_ne_zero (m : ι → ℤ) {u : Z} (hu : ∀ i, 0 < (u i).re) :
    complexDiagonalGamma m u ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl ?_)))
    (Complex.Gamma_ne_zero_of_re_pos ?_)
  · exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  · simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    positivity [hu i]

/-- The product Tate equation on the product of common strips, with the scalar
Gaussian normalization of the complex Tate statement. -/
theorem complexDiagonalTateEquation_strip (hTate : ComplexArchimedeanTateStatement)
    (Φ Φf : SchwartzMap Z ℂ) (hΦ : (Φf : Z → ℂ) = complexCoordinateFourier 1 Φ)
    (m : ι → ℤ) {u : Z} (hu₀ : ∀ i, 0 < (u i).re) (hu₁ : ∀ i, (u i).re < 1) :
    complexDiagonalZeta 1 Φf (-m) (1 - u) / complexDiagonalGamma (-m) (1 - u) =
      complexDiagonalStandardEpsilon m * (complexDiagonalZeta 1 Φ m u / complexDiagonalGamma m u) := by
  have hv (i : ι) : 0 < ((1 - u) i).re := by
    simpa only [Pi.sub_apply, Pi.one_apply, Complex.sub_re, Complex.one_re] using sub_pos.mpr (hu₁ i)
  let g (q : ℤ) := (exists_schwartz_tateGaussian hTate q).choose
  have hg (q : ℤ) : (g q : ℂ → ℂ) = tateGaussian q :=
    (exists_schwartz_tateGaussian hTate q).choose_spec
  let Ψ := finiteTensor (fun i => g (m i))
  let Ψf := finiteTensor (fun i => (Complex.I ^ (m i).natAbs) • g (-(m i)))
  have hΨ : (Ψf : Z → ℂ) = complexCoordinateFourier 1 Ψ := by
    funext z
    rw [complexCoordinateFourier_finiteTensor]
    simp only [Ψf, finiteTensor_apply, smul_apply, smul_eq_mul, hg,
      complexScalarFourier_tateGaussian hTate]
  have hprimal : complexDiagonalZeta 1 Ψ m u = complexDiagonalGamma m u := by
    rw [complexDiagonalZeta_finiteTensor _ _ _ hu₀]
    unfold complexDiagonalGamma
    exact Finset.prod_congr rfl fun i _ => by simpa only [hg] using integral_tateGaussian hTate (m i) (hu₀ i)
  have hdual : complexDiagonalZeta 1 Ψf (-m) (1 - u) =
      complexDiagonalStandardEpsilon m * complexDiagonalGamma (-m) (1 - u) := by
    rw [complexDiagonalZeta_finiteTensor _ _ _ hv]
    unfold complexDiagonalStandardEpsilon complexDiagonalGamma
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    change (∫ z, (Complex.I ^ (m i).natAbs * g (-(m i)) z) *
      complexMellinWeight ((-m) i) ((1 - u) i) z ∂(complexSelfDualMeasure 1).measure) = _
    rw [← Pi.neg_apply m i]
    simp only [hg, Pi.neg_apply, mul_assoc, integral_const_mul]
    rw [integral_tateGaussian hTate (-(m i)) (hv i)]
  have h := complexDiagonalTateIdentity 1 Φ Ψ Φf Ψf hΦ hΨ m hu₀ hu₁
  rw [hprimal, hdual] at h
  apply (div_eq_iff (complexDiagonalGamma_ne_zero (-m) hv)).mpr
  rw [mul_assoc, div_mul_eq_mul_div, ← mul_div_assoc, eq_div_iff (complexDiagonalGamma_ne_zero m hu₀)]
  calc
    _ = complexDiagonalZeta 1 Φ m u *
        (complexDiagonalStandardEpsilon m * complexDiagonalGamma (-m) (1 - u)) := h.symm
    _ = _ := by ring

end Langlands.GodementJacquet

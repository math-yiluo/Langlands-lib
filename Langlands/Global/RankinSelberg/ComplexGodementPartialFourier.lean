import Langlands.Analysis.SchwartzPartialFourier
import Langlands.Global.RankinSelberg.ComplexGodementColumnChange

/-! # Complex last-column partial Fourier and the iterated Godement integral -/

noncomputable section

open MeasureTheory
open scoped Classical ENNReal FourierTransform Matrix.Norms.Elementwise NNReal RealInnerProductSpace
  SchwartzMap
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter
  complexScaledCharacter_apply)
open Langlands.HarmonicAnalysis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementPartialFourier

variable {m : ℕ}
local notation "Square" => Matrix (Fin m) (Fin m) ℂ
local notation "Rect" => Matrix (Fin m) (Fin (m + 1)) ℂ
local notation "Vec" => Fin m → ℂ
local notation "SqE" => EuclideanSpace ℝ (Fin (Module.finrank ℝ Square))
local notation "ColE" => PiLp 2 (fun _ : Fin m => ℂ)

private def splitEquiv : Rect ≃L[ℝ] (Square × Vec) where
  toFun X := (rectangularFirstColumns X, rectangularLastColumn X)
  invFun p := rectangularJoin p.1 p.2
  left_inv := rectangularJoin_split
  right_inv p := by simp
  map_add' X Y := rfl
  map_smul' c X := rfl
  continuous_toFun := continuous_rectangularFirstColumns.prodMk continuous_rectangularLastColumn
  continuous_invFun := continuous_rectangularJoin

set_option synthInstance.maxHeartbeats 120000 in
private def squareEquiv : Square ≃L[ℝ] SqE :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

private abbrev rowEquiv : ColE ≃L[ℝ] Vec := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℂ)

private def rectEquiv : Rect ≃L[ℝ] SqE × ColE :=
  splitEquiv.trans (squareEquiv.prodCongr rowEquiv.symm)

private def freqScalar (a : ℂˣ) : ℂ ≃L[ℝ] ℂ :=
  let u := Units.mk0 ((-2 : ℂ) * (a : ℂ)) (mul_ne_zero (by norm_num) a.ne_zero)
  ((ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ) u).restrictScalars ℝ).trans
    Complex.conjLIE.toContinuousLinearEquiv

private theorem freqScalar_apply (a : ℂˣ) (z : ℂ) :
    freqScalar a z = star ((-2 : ℂ) * (a : ℂ) * z) := rfl

private def frequency (a : ℂˣ) : Vec ≃L[ℝ] ColE :=
  (ContinuousLinearEquiv.piCongrRight fun _ : Fin m => freqScalar a).trans rowEquiv.symm

private theorem frequency_apply (a : ℂˣ) (ξ : Vec) (j : Fin m) :
    frequency a ξ j = star ((-2 : ℂ) * (a : ℂ) * ξ j) := by
  change freqScalar a (ξ j) = _
  exact freqScalar_apply a (ξ j)

private theorem trace_eq_neg_inner (a : ℂˣ) (ξ : Vec) (v : ColE) :
    Algebra.trace ℝ ℂ ((a : ℂ) * ∑ j, ξ j * rowEquiv v j) = -inner ℝ v (frequency a ξ) := by
  rw [Algebra.trace_complex_apply, PiLp.inner_apply, Finset.mul_sum, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.inner, frequency_apply, Complex.star_def, ← map_mul]
  change 2 * (((a : ℂ) * (ξ j * v j)).re) = -((starRingEnd ℂ ((-2 : ℂ) * (a : ℂ) * ξ j * v j)).re)
  rw [Complex.conj_re, show (-2 : ℂ) * (a : ℂ) * ξ j * v j =
    (((-2 : ℝ)) : ℂ) * ((a : ℂ) * (ξ j * v j)) by push_cast; ring,
    Complex.re_ofReal_mul]
  ring

private def freqRectEquiv (a : ℂˣ) : Rect ≃L[ℝ] SqE × ColE :=
  splitEquiv.trans (squareEquiv.prodCongr (frequency a))

private def rowNorm (μ : AdditiveHaarMeasure ℂ) (m : ℕ) : ℝ≥0 := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  exact Measure.addHaarScalarFactor ((rowMeasure μ m).map (rowEquiv (m := m)).symm) volume

private theorem rowNorm_eq (μ : AdditiveHaarMeasure ℂ) :
    (rowMeasure μ m).map (rowEquiv (m := m)).symm = rowNorm μ m • (volume : Measure ColE) := by
  have : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have : SigmaFinite μ.measure := inferInstance
  exact Measure.isAddLeftInvariant_eq_smul ((rowMeasure μ m).map (rowEquiv (m := m)).symm) volume

/-- The Schwartz representative of the positive trace transform in the last column. -/
def partialSchwartz (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ) (Φ : 𝓢(Rect, ℂ)) : 𝓢(Rect, ℂ) :=
  ((rowNorm μ m : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (freqRectEquiv a)
    (Langlands.Analysis.SchwartzPartialFourier.transform
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rectEquiv.symm Φ))

@[simp]
theorem partialSchwartz_apply (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ) (Φ : 𝓢(Rect, ℂ)) (X : Rect) :
    partialSchwartz a μ Φ X = partialFourierPlusIntegral (complexScaledCharacter a) μ Φ X := by
  let x := rectangularFirstColumns X
  let ξ := rectangularLastColumn X
  let c := rowNorm μ m
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rectEquiv.symm Φ
  let e := rowEquiv (m := m)
  let f : ColE → ℂ := fun v => Φ (rectangularJoin x (e v)) *
    (complexScaledCharacter a).complex (∑ j, ξ j * e v j)
  change (c : ℂ) • Langlands.Analysis.SchwartzPartialFourier.transform P (squareEquiv x, frequency a ξ) = _
  rw [Langlands.Analysis.SchwartzPartialFourier.transform_apply, Real.fourier_eq]
  have hf (v : ColE) :
      Real.fourierChar (-inner ℝ v (frequency a ξ)) • P (squareEquiv x, v) = f v := by
    have hP : P (squareEquiv x, v) = Φ (rectangularJoin x (e v)) := by
      simp [P, rectEquiv, splitEquiv, e]
      rfl
    rw [hP, ← trace_eq_neg_inner, Circle.smul_def, smul_eq_mul, mul_comm]
    simp only [f, UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply]
    rfl
  simp_rw [hf]
  calc
    _ = ∫ v, f v ∂(rowMeasure μ m).map e.symm := by
      rw [rowNorm_eq]
      change (c : ℂ) • _ = ∫ v, f v ∂(c : ℝ≥0∞) • volume
      rw [integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul, smul_eq_mul]
    _ = ∫ u, f (e.symm u) ∂rowMeasure μ m := integral_map_equiv e.symm.toHomeomorph.toMeasurableEquiv f
    _ = _ := by
      unfold partialFourierPlusIntegral
      simp only [f, ContinuousLinearEquiv.apply_symm_apply, rowPairing]
      rfl

open ComplexGodementColumnChange (iteratedKernel complexGodementColumnChange)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

/-- The iterated integral of (7.6) uses the conjugate of the Whittaker character in the
column integral. It is absolutely convergent in the outer variable for all exponents and
entire at fixed Schwartz test and smaller-rank model vector. -/
def ComplexGodementIteratedIntegralStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (ν : Measure (Langlands.GeneralLinear (r + 1) ℂ)), ν.IsHaarMeasure →
  ∀ (μ : AdditiveHaarMeasure ℂ) (d : ComplexCharacterData)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ, ℂ))
    (W : complexWhittakerModel r ds a),
    (∀ s, Integrable (iteratedKernel (complexScaledCharacter (-a)) μ d Φ W.val s) ν) ∧
      Differentiable ℂ (fun s => ∫ h, iteratedKernel (complexScaledCharacter (-a)) μ d Φ W.val s h ∂ν)

theorem complexGodementIteratedIntegral : ComplexGodementIteratedIntegralStatement := by
  intro r ds a ν hν μ d Φ W
  exact complexGodementColumnChange r ds a ν hν (complexScaledCharacter (-a)) μ d Φ
    (partialSchwartz (-a) μ Φ) (partialSchwartz_apply (-a) μ Φ) W

end Langlands.Global.RankinSelbergGlobal.ComplexGodementPartialFourier

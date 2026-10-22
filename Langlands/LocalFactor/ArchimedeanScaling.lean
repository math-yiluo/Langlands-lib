import Langlands.LocalFactor.ArchimedeanAttachment
import Langlands.HarmonicAnalysis.CharacterTransport
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Explicit character and Haar changes of archimedean block epsilon factors

The scalar and positive measure scale remain supplied data. The spectral
normalization is a twist by the normalized absolute value to the power `s`.
-/

noncomputable section

namespace Langlands.LocalFactor.Archimedean

open Langlands.HarmonicAnalysis

/-- The plus character `exp(2*pi*i*x)` on the real field. -/
def realStandardCharacter : UnitaryAdditiveCharacter ℝ where
  toAddChar := Real.fourierChar
  continuous_toFun := Real.continuous_fourierChar
  nontrivial := Real.fourierChar_ne_one

/-- The standard complex character is the actual field-trace pullback. -/
def complexStandardCharacter : UnitaryAdditiveCharacter ℂ := by
  letI : IsModuleTopology ℝ ℂ := isModuleTopologyOfFiniteDimensional
  exact realStandardCharacter.tracePullback

/-- Standard real additive measure: Lebesgue measure. -/
def realStandardMeasure : AdditiveHaarMeasure ℝ where
  measure := MeasureTheory.volume
  isAddHaar := inferInstance
  regular := inferInstance

/-- Standard complex additive measure: twice Euclidean area. -/
def complexStandardMeasure : AdditiveHaarMeasure ℂ :=
  ({ measure := MeasureTheory.volume
     isAddHaar := inferInstance
     regular := inferInstance } : AdditiveHaarMeasure ℂ).scale 2 (by norm_num)

/-- Actual changed real character; the measure is not changed by this operation. -/
def realScaledCharacter (a : ℝˣ) : UnitaryAdditiveCharacter ℝ :=
  realStandardCharacter.scale a

/-- Actual changed complex trace character. -/
def complexScaledCharacter (a : ℂˣ) : UnitaryAdditiveCharacter ℂ :=
  complexStandardCharacter.scale a

/-- A positive multiple of the fixed real standard measure. -/
def realScaledMeasure (c : NNReal) (hc : 0 < c) : AdditiveHaarMeasure ℝ :=
  realStandardMeasure.scale c hc

/-- A positive multiple of the fixed complex standard measure. -/
def complexScaledMeasure (c : NNReal) (hc : 0 < c) : AdditiveHaarMeasure ℂ :=
  complexStandardMeasure.scale c hc

@[simp]
theorem realScaledCharacter_apply (a : ℝˣ) (x : ℝ) :
    realScaledCharacter a x = Real.fourierChar ((a : ℝ) * x) := rfl

@[simp]
theorem complexScaledCharacter_apply (a : ℂˣ) (z : ℂ) :
    complexScaledCharacter a z =
      Real.fourierChar (Algebra.trace ℝ ℂ ((a : ℂ) * z)) := rfl

@[simp]
theorem realScaledMeasure_measure (c : NNReal) (hc : 0 < c) :
    (realScaledMeasure c hc).measure = c • MeasureTheory.volume := rfl

@[simp]
theorem complexScaledMeasure_measure (c : NNReal) (hc : 0 < c) :
    (complexScaledMeasure c hc).measure =
      (c * 2) • (MeasureTheory.volume : MeasureTheory.Measure ℂ) := by
  exact smul_smul c (2 : NNReal) _

private def positiveScale (c : NNReal) (hc : 0 < c) : ℂˣ :=
  Units.mk0 (c : ℂ) (by exact_mod_cast hc.ne')

private def positivePower (r : ℝ) (hr : 0 < r) (s : ℂ) : ℂˣ :=
  Units.mk0 ((r : ℂ) ^ s)
    (Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast hr.ne')))

/-- Inclusion of real units into complex units. -/
def realToComplex (a : ℝˣ) : ℂˣ := Units.map Complex.ofRealHom.toMonoidHom a

/-- The sign of a real unit, as a complex unit. -/
def realSign (a : ℝˣ) : ℂˣ :=
  Units.mk0 (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ)
    (by exact_mod_cast div_ne_zero a.ne_zero (abs_ne_zero.mpr a.ne_zero))

@[simp]
theorem coe_realSign (a : ℝˣ) :
    (realSign a : ℂ) = (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) := rfl

namespace RealCharacterData

/-- Epsilon of this real block twisted by `|.|^s`, for the character
`realScaledCharacter a` and fixed measure `realScaledMeasure c hc`. -/
def epsilon (d : RealCharacterData) (a : ℝˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) : ℂˣ :=
  positiveScale c hc * d.character a *
    positivePower |(a : ℝ)| (abs_pos.mpr a.ne_zero) (s - 1) * d.standardEpsilon

@[simp]
theorem coe_epsilon (d : RealCharacterData) (a : ℝˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) :
    (d.epsilon a c hc s : ℂ) = (c : ℂ) * (d.character a : ℂ) *
      ((|(a : ℝ)| : ℝ) : ℂ) ^ (s - 1) * Complex.I ^ d.parity.val := rfl

theorem epsilon_ne_zero (d : RealCharacterData) (a : ℝˣ) (c : NNReal)
    (hc : 0 < c) (s : ℂ) : (d.epsilon a c hc s : ℂ) ≠ 0 :=
  (d.epsilon a c hc s).ne_zero

theorem differentiable_epsilon (d : RealCharacterData) (a : ℝˣ) (c : NNReal)
    (hc : 0 < c) : Differentiable ℂ (fun s => (d.epsilon a c hc s : ℂ)) := by
  simp only [coe_epsilon]
  apply Differentiable.mul_const
  apply Differentiable.const_mul
  exact (differentiable_id.sub_const 1).const_cpow
    (.inl (by exact_mod_cast abs_ne_zero.mpr a.ne_zero))

@[simp]
theorem epsilon_standard (d : RealCharacterData) (s : ℂ) :
    d.epsilon 1 1 zero_lt_one s = d.standardEpsilon := by
  apply Units.ext
  simp

/-- Changing the positive Haar scale multiplies the rank-one factor by that scale. -/
theorem epsilon_measure_scale (d : RealCharacterData) (a : ℝˣ)
    (c b : NNReal) (hc : 0 < c) (hb : 0 < b) (s : ℂ) :
    (d.epsilon a (b * c) (mul_pos hb hc) s : ℂ) =
      (b : ℂ) * (d.epsilon a c hc s : ℂ) := by
  simp only [coe_epsilon, NNReal.coe_mul, Complex.ofReal_mul]
  ring

end RealCharacterData

namespace ComplexCharacterData

/-- Epsilon of this complex block twisted by the normalized absolute value
`‖.‖^(2*s)`, for `complexScaledCharacter a` and `complexScaledMeasure c hc`. -/
def epsilon (d : ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) : ℂˣ :=
  positiveScale c hc * d.character a *
    positivePower ‖(a : ℂ)‖ (norm_pos_iff.mpr a.ne_zero) (2 * (s - 1)) *
      d.standardEpsilon

@[simp]
theorem coe_epsilon (d : ComplexCharacterData) (a : ℂˣ) (c : NNReal) (hc : 0 < c)
    (s : ℂ) :
    (d.epsilon a c hc s : ℂ) = (c : ℂ) * (d.character a : ℂ) *
      (‖(a : ℂ)‖ : ℂ) ^ (2 * (s - 1)) * Complex.I ^ d.weight.natAbs := rfl

theorem epsilon_ne_zero (d : ComplexCharacterData) (a : ℂˣ) (c : NNReal)
    (hc : 0 < c) (s : ℂ) : (d.epsilon a c hc s : ℂ) ≠ 0 :=
  (d.epsilon a c hc s).ne_zero

theorem differentiable_epsilon (d : ComplexCharacterData) (a : ℂˣ) (c : NNReal)
    (hc : 0 < c) : Differentiable ℂ (fun s => (d.epsilon a c hc s : ℂ)) := by
  simp only [coe_epsilon]
  apply Differentiable.mul_const
  apply Differentiable.const_mul
  exact ((differentiable_id.sub_const 1).const_mul 2).const_cpow
    (.inl (by exact_mod_cast norm_ne_zero_iff.mpr a.ne_zero))

@[simp]
theorem epsilon_standard (d : ComplexCharacterData) (s : ℂ) :
    d.epsilon 1 1 zero_lt_one s = d.standardEpsilon := by
  apply Units.ext
  simp

theorem epsilon_measure_scale (d : ComplexCharacterData) (a : ℂˣ)
    (c b : NNReal) (hc : 0 < c) (hb : 0 < b) (s : ℂ) :
    (d.epsilon a (b * c) (mul_pos hb hc) s : ℂ) =
      (b : ℂ) * (d.epsilon a c hc s : ℂ) := by
  simp only [coe_epsilon, NNReal.coe_mul, Complex.ofReal_mul]
  ring

/-- Scalar determinant character of the real induction: sign times restriction
of the inducing character to the real units. -/
def realInducedDeterminant (d : ComplexCharacterData) (a : ℝˣ) : ℂˣ :=
  realSign a * d.character (realToComplex a)

@[simp]
theorem coe_realInducedDeterminant (d : ComplexCharacterData) (a : ℝˣ) :
    (d.realInducedDeterminant a : ℂ) =
      (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) * (d.character (realToComplex a) : ℂ) := rfl

/-- Epsilon of the actual real induction block, with real scalar and real
Haar scale; its rank is two, including for weight zero. -/
def realInducedEpsilon (d : ComplexCharacterData) (a : ℝˣ) (c : NNReal)
    (hc : 0 < c) (s : ℂ) : ℂˣ :=
  positiveScale c hc ^ 2 * d.realInducedDeterminant a *
    positivePower |(a : ℝ)| (abs_pos.mpr a.ne_zero) (2 * (s - 1)) *
      d.realInducedStandardEpsilon

@[simp]
theorem coe_realInducedEpsilon (d : ComplexCharacterData) (a : ℝˣ) (c : NNReal)
    (hc : 0 < c) (s : ℂ) :
    (d.realInducedEpsilon a c hc s : ℂ) = (c : ℂ) ^ 2 *
      ((((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ) * (d.character (realToComplex a) : ℂ)) *
      ((|(a : ℝ)| : ℝ) : ℂ) ^ (2 * (s - 1)) * Complex.I ^ (d.weight.natAbs + 1) := rfl

theorem realInducedEpsilon_ne_zero (d : ComplexCharacterData) (a : ℝˣ)
    (c : NNReal) (hc : 0 < c) (s : ℂ) : (d.realInducedEpsilon a c hc s : ℂ) ≠ 0 :=
  (d.realInducedEpsilon a c hc s).ne_zero

theorem differentiable_realInducedEpsilon (d : ComplexCharacterData) (a : ℝˣ)
    (c : NNReal) (hc : 0 < c) :
    Differentiable ℂ (fun s => (d.realInducedEpsilon a c hc s : ℂ)) := by
  simp only [coe_realInducedEpsilon]
  apply Differentiable.mul_const
  apply Differentiable.const_mul
  exact ((differentiable_id.sub_const 1).const_mul 2).const_cpow
    (.inl (by exact_mod_cast abs_ne_zero.mpr a.ne_zero))

@[simp]
theorem realInducedEpsilon_standard (d : ComplexCharacterData) (s : ℂ) :
    d.realInducedEpsilon 1 1 zero_lt_one s = d.realInducedStandardEpsilon := by
  apply Units.ext
  simp [realToComplex]

/-- The rank-two induction uses the square of the Haar scale. -/
theorem realInducedEpsilon_measure_scale (d : ComplexCharacterData) (a : ℝˣ)
    (c b : NNReal) (hc : 0 < c) (hb : 0 < b) (s : ℂ) :
    (d.realInducedEpsilon a (b * c) (mul_pos hb hc) s : ℂ) =
      (b : ℂ) ^ 2 * (d.realInducedEpsilon a c hc s : ℂ) := by
  simp only [coe_realInducedEpsilon, NNReal.coe_mul, Complex.ofReal_mul]
  ring

end ComplexCharacterData

end Langlands.LocalFactor.Archimedean

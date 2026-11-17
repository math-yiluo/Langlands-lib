import Langlands.Global.RankinSelberg.RealRankZeroHaar
import Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement
import Langlands.LocalFactor.Archimedean.RealTateZeta
import Langlands.LocalFactor.Archimedean.Statement
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-! # The rank-one real local Rankin–Selberg functional equation, from Tate's theory

For `W = C · χ ∘ det` and `W' = C' · χ' ∘ det` on `GL₁(ℝ)`, the equal-rank local integrals
`Ψ(s; W, W', Φ)` and `Ψ(s; W̃, W̃', Φ̂)` are multiples of real Tate zeta integrals of the
restriction of `Φ` to the line and of its Fourier transform, and the local functional
equation of `RealEqualFunctionalEquationStatement` at `r = 0` follows from
`RealArchimedeanTateStatement`. See the paired Markdown.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Filter
open scoped NNReal ENNReal SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealRankZero

open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ArchimedeanLocal

attribute [local instance] unitsMeasurable unitsBorel rankZeroGLMeasurable rankZeroGLBorel
  rankZeroNMeasurable rankZeroNBorel rankZeroQMeasurable rankZeroQBorel

local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

/-! ### The line restriction of a Schwartz function on `ℝ¹` -/

/-- The Schwartz function `x ↦ Φ(x)` on `ℝ` attached to `Φ` on `ℝ^1`. -/
def lineSchwartz (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.funUnique (Fin (0 + 1)) ℝ ℝ).symm Φ

theorem lineSchwartz_apply (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) (x : ℝ) :
    lineSchwartz Φ x = Φ (fun _ => x) := rfl

/-- The scaled Fourier transform of the real Tate statement:
`y ↦ c ∫ exp(2π i a x y) f(x) dx`. -/
def tateFourier (a : ℝ) (c : ℝ≥0) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  (c : ℂ) * ∫ x, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a * x * y : ℝ)) * f x

theorem realFourierTransform_const (a : ℝˣ) (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) (y : ℝ) :
    realFourierTransform a (Φ : (Fin (0 + 1) → ℝ) → ℂ) (fun _ => y) =
      tateFourier a (NNReal.sqrt ‖(a : ℝ)‖₊) (lineSchwartz Φ) y := by
  rw [realFourierTransform, ArchimedeanLocal.fourierTransform, realSelfDualMeasure,
    realScaledMeasure_measure]
  have hmp := (measurePreserving_funUnique
    ((NNReal.sqrt ‖(a : ℝ)‖₊) • (volume : Measure ℝ)) (Fin (0 + 1))).symm
  refine (hmp.integral_comp' _).symm.trans ?_
  rw [integral_smul_nnreal_measure, tateFourier, NNReal.smul_def, Complex.real_smul]
  congr 2
  funext x
  have hx : (MeasurableEquiv.funUnique (Fin (0 + 1)) ℝ).symm x = fun _ => x := rfl
  rw [hx, Fin.sum_univ_one, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    realScaledCharacter_apply, Real.fourierChar_apply, lineSchwartz_apply, mul_comm]
  congr 2
  push_cast
  ring

/-! ### Evaluation at scalar matrices -/

theorem determinant_tateScalarEquiv (u : ℝˣ) :
    GeneralLinear.determinant (Langlands.GodementJacquet.tateScalarEquiv ℝ u) = u :=
  (Langlands.GodementJacquet.tateScalarEquiv ℝ).symm_apply_apply u

theorem det_val_tateScalarEquiv (u : ℝˣ) :
    Matrix.det (Langlands.GodementJacquet.tateScalarEquiv ℝ u).val = u := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact congrArg Units.val (determinant_tateScalarEquiv u)

theorem lastRow_tateScalarEquiv (u : ℝˣ) :
    lastRow (n := 0) (Langlands.GodementJacquet.tateScalarEquiv ℝ u) = fun _ => (u : ℝ) := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  change (Matrix.GeneralLinearGroup.scalar (Fin 1) u : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = u
  simp [Matrix.GeneralLinearGroup.coe_scalar]

theorem detPower_tateScalarEquiv (u : ℝˣ) (s : ℂ) :
    ArchimedeanLocal.detPower realNormalizedAbs (Langlands.GodementJacquet.tateScalarEquiv ℝ u) s =
      ((|(u : ℝ)| : ℝ) : ℂ) ^ s := by
  have hpos : 0 < |(u : ℝ)| := abs_pos.mpr u.ne_zero
  rw [ArchimedeanLocal.detPower, realNormalizedAbs, det_val_tateScalarEquiv,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    ← Complex.ofReal_log hpos.le, mul_comm]

theorem dualFunction_apply (W : Langlands.GeneralLinear (0 + 1) ℝ → ℂ)
    (g : Langlands.GeneralLinear (0 + 1) ℝ) :
    ArchimedeanLocal.dualFunction (0 + 1) W g = W (GeneralLinear.inverseTranspose 1 ℝ g) := by
  rw [ArchimedeanLocal.dualFunction]
  congr 1
  rw [show GeneralLinear.weylLong (0 + 1) ℝ = 1 from
    Langlands.RankinSelberg.RankOneGammaTwist.weylLong_one, one_mul]

/-! ### Sign and absolute-value algebra -/

/-- The sign `x / |x|` of a real number, as a complex number. -/
abbrev sgn (x : ℝ) : ℂ := ((x / |x| : ℝ) : ℂ)

theorem character_mul_character (c c' : RealCharacterData) (u : ℝˣ) :
    (c.character u : ℂ) * (c'.character u : ℂ) =
      sgn u ^ (c.mul c').parity.val * ((|(u : ℝ)| : ℝ) : ℂ) ^ (c.mul c').exponent := by
  rw [← (c.mul c').character_eq]
  rfl

theorem character_inv_mul_character_inv (c c' : RealCharacterData) (u : ℝˣ) :
    ((c.character u : ℂ))⁻¹ * ((c'.character u : ℂ))⁻¹ =
      sgn u ^ (c.mul c').parity.val * ((|(u : ℝ)| : ℝ) : ℂ) ^ (-(c.mul c').exponent) := by
  rw [← mul_inv, character_mul_character, mul_inv, Complex.cpow_neg]
  congr 1
  exact inv_eq_of_mul_eq_one_right (RealTate.sign_pow_mul_self u.ne_zero _)

theorem character_inv_apply (c : RealCharacterData) (u : ℝˣ) :
    (c.character u⁻¹ : ℂ) = (c.character u : ℂ)⁻¹ := by
  rw [map_inv, Units.val_inv_eq_inv_val]

theorem abs_cpow_shift {x : ℝ} (hx : x ≠ 0) (s t : ℂ) :
    ((|x|⁻¹ : ℝ) : ℂ) * (((|x| : ℝ) : ℂ) ^ t * ((|x| : ℝ) : ℂ) ^ s) =
      ((|x| : ℝ) : ℂ) ^ (s + t - 1) := by
  have hne := RealTate.abs_cpow_ne_zero hx
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_one, Complex.cpow_add _ _ hne, Complex.ofReal_inv]
  ring

/-! ### The integrands on the line -/

section Integrands

variable (c c' : RealCharacterData) {W W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ} {C C' : ℂ}

/-- The integrand of `Ψ(s; W, W', Φ)`, transported to `ℝ` and multiplied by `|x|⁻¹`, is a
multiple of the real Tate integrand of the line restriction of `Φ`. -/
theorem extend_equalIntegrand
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) (s : ℂ) (x : ℝ) :
    ((|x|⁻¹ : ℝ) : ℂ) * unitsExtend (realEqualIntegrand W W' Φ s) x =
      C * C' * RealTate.integrand (lineSchwartz Φ) (c.mul c').parity
        (s + (c.mul c').exponent) x := by
  by_cases hx : x = 0
  · simp [hx, unitsExtend, RealTate.integrand_zero]
  · have hu : x = (Units.mk0 x hx : ℝ) := rfl
    rw [hu, unitsExtend_val]
    set u := Units.mk0 x hx
    simp only [realEqualIntegrand, ArchimedeanLocal.equalIntegrand, quotientUnits_symm_out]
    rw [hW, hW', determinant_tateScalarEquiv, lastRow_tateScalarEquiv,
      detPower_tateScalarEquiv, RealTate.integrand, ite_eq_right_of_eq_false _ _ (eq_false u.ne_zero), lineSchwartz_apply,
      ← abs_cpow_shift u.ne_zero]
    have hχ := character_mul_character c c' u
    calc _ = C * C' * ((c.character u : ℂ) * (c'.character u : ℂ)) * Φ (fun _ => (u : ℝ)) *
          ((|(u : ℝ)|⁻¹ : ℝ) : ℂ) * ((|(u : ℝ)| : ℝ) : ℂ) ^ s := by ring
      _ = _ := by rw [hχ]; ring

/-- The integrand of `Ψ(s; W̃, W̃', Φ̂)`, transported to `ℝ` and multiplied by `|x|⁻¹`, is a
multiple of the real Tate integrand of the scaled Fourier transform of the line restriction. -/
theorem extend_dualIntegrand
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (a : ℝˣ) (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) (s : ℂ) (x : ℝ) :
    ((|x|⁻¹ : ℝ) : ℂ) * unitsExtend (realEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
        (ArchimedeanLocal.dualFunction (0 + 1) W') (realFourierTransform a Φ) s) x =
      C * C' * RealTate.integrand (tateFourier a (NNReal.sqrt ‖(a : ℝ)‖₊) (lineSchwartz Φ))
        (c.mul c').parity (s + -(c.mul c').exponent) x := by
  by_cases hx : x = 0
  · simp [hx, unitsExtend, RealTate.integrand_zero]
  · have hu : x = (Units.mk0 x hx : ℝ) := rfl
    rw [hu, unitsExtend_val]
    set u := Units.mk0 x hx
    simp only [realEqualIntegrand, ArchimedeanLocal.equalIntegrand, quotientUnits_symm_out,
      dualFunction_apply]
    rw [hW, hW', Langlands.RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose,
      determinant_tateScalarEquiv, lastRow_tateScalarEquiv, realFourierTransform_const,
      detPower_tateScalarEquiv, RealTate.integrand, ite_eq_right_of_eq_false _ _ (eq_false u.ne_zero),
      ← abs_cpow_shift u.ne_zero, character_inv_apply, character_inv_apply]
    have hχ := character_inv_mul_character_inv c c' u
    calc _ = C * C' * ((c.character u : ℂ)⁻¹ * (c'.character u : ℂ)⁻¹) *
          tateFourier a (NNReal.sqrt ‖(a : ℝ)‖₊) (lineSchwartz Φ) u *
          ((|(u : ℝ)|⁻¹ : ℝ) : ℂ) * ((|(u : ℝ)| : ℝ) : ℂ) ^ s := by ring
      _ = _ := by rw [hχ]; ring

variable {D : RealQuotientMeasureData 0} {κ : ℝ≥0}

theorem equalIntegral_eq (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) (s : ℂ) :
    realEqualIntegral D W W' Φ s = (κ : ℂ) * (C * C' *
      RealTate.zeta (lineSchwartz Φ) (c.mul c').parity (s + (c.mul c').exponent)) := by
  change ∫ q, realEqualIntegrand W W' Φ s q ∂D.measure = _
  rw [integral_eq hκ, RealTate.zeta, ← integral_const_mul (C * C')]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => extend_equalIntegrand c c' hW hW' Φ s x)

theorem equalDualIntegral_eq (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (a : ℝˣ) (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) (s : ℂ) :
    realEqualDualIntegral a D W W' Φ s = (κ : ℂ) * (C * C' *
      RealTate.zeta (tateFourier a (NNReal.sqrt ‖(a : ℝ)‖₊) (lineSchwartz Φ)) (c.mul c').parity
        (s + -(c.mul c').exponent)) := by
  change ∫ q, realEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
    (ArchimedeanLocal.dualFunction (0 + 1) W') (realFourierTransform a Φ) s q ∂D.measure = _
  rw [integral_eq hκ, RealTate.zeta, ← integral_const_mul (C * C')]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => extend_dualIntegrand c c' hW hW' a Φ s x)

theorem integrable_equalIntegrand (hκ0 : κ ≠ 0)
    (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) {s : ℂ} (hs : 0 < (s + (c.mul c').exponent).re) :
    Integrable (realEqualIntegrand W W' Φ s) D.measure :=
  (integrable_iff hκ0 hκ _).mpr
    (((RealTate.integrable_integrand (lineSchwartz Φ) _ hs).const_mul (C * C')).congr
      (ae_of_all _ fun x => (extend_equalIntegrand c c' hW hW' Φ s x).symm))

theorem integrable_dualIntegrand (hκ0 : κ ≠ 0)
    (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (a : ℝˣ) (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) (g : 𝓢(ℝ, ℂ))
    (hg : (g : ℝ → ℂ) = tateFourier a (NNReal.sqrt ‖(a : ℝ)‖₊) (lineSchwartz Φ))
    {s : ℂ} (hs : 0 < (s + -(c.mul c').exponent).re) :
    Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
      (ArchimedeanLocal.dualFunction (0 + 1) W') (realFourierTransform a Φ) s) D.measure := by
  refine (integrable_iff hκ0 hκ _).mpr
    (((RealTate.integrable_integrand g (c.mul c').parity hs).const_mul (C * C')).congr
      (ae_of_all _ fun x => ?_))
  beta_reduce
  rw [extend_dualIntegrand c c' hW hW' a Φ s x, hg]

end Integrands

/-! ### Rank-one factors -/

theorem realPairBlocks_character (c c' : RealCharacterData) :
    realPairBlocks [RealBlock.character c] [RealBlock.character c'] =
      [RealBlock.character (c.mul c')] := rfl

theorem realPairLFactor_character (c c' : RealCharacterData) (s : ℂ) :
    (realPairLFactor [RealBlock.character c] [RealBlock.character c']).denominator s =
      (Complex.Gammaℝ (s + ((c.mul c').exponent + ((c.mul c').parity.val : ℂ))))⁻¹ := by
  rw [realPairLFactor, realPairBlocks_character, realLFactor_singleton,
    RealBlock.lFactor_character, ReciprocalEntire.denominator_shift]
  rfl

theorem realPairEpsilon_character (c c' : RealCharacterData) (a : ℝˣ) (c0 : ℝ≥0)
    (hc : 0 < c0) (s : ℂ) :
    (realPairEpsilon [RealBlock.character c] [RealBlock.character c'] a c0 hc s : ℂ) =
      (c0 : ℂ) * sgn a ^ (c.mul c').parity.val *
        ((|(a : ℝ)| : ℝ) : ℂ) ^ (s + (c.mul c').exponent - 1) *
        Complex.I ^ (c.mul c').parity.val := by
  rw [realPairEpsilon, realPairBlocks_character, realEpsilon_singleton]
  change (((c.mul c').epsilon a c0 hc s : ℂˣ) : ℂ) = _
  rw [RealCharacterData.coe_epsilon, (c.mul c').character_eq]
  have hne := RealTate.abs_cpow_ne_zero a.ne_zero
  rw [show s + (c.mul c').exponent - 1 = (c.mul c').exponent + (s - 1) by ring,
    Complex.cpow_add _ _ hne]
  ring

/-- The entire function `s ↦ Γℝ(1 - s - t + q)⁻¹`. -/
def reflectedGamma (t q : ℂ) : ReciprocalEntire where
  denominator := fun s => (Complex.Gammaℝ (1 - s - t + q))⁻¹
  entire := by
    have h : Differentiable ℂ (fun s : ℂ => 1 - s - t + q) := by fun_prop
    exact Complex.differentiable_Gammaℝ_inv.comp h
  nonzero := ⟨q - t, by rw [show 1 - (q - t) - t + q = 1 by ring]; simp⟩

/-! ### The rank-one local functional equation -/

/-- **Rank-one real local functional equation.** Let `W = C · χ_c ∘ det` and
`W' = C' · χ_{c'} ∘ det` on `GL₁(ℝ)`, and let the dual characters `cd, cd'` satisfy
`χ_{cd} χ_{cd'} = (χ_c χ_{c'})⁻¹` at the level of parity and exponent. Then the conclusions
of `RealEqualFunctionalEquationStatement` at `r = 0` hold for the single-character
parameters `[c], [c'], [cd], [cd']` (the sign factor `realMinusOneScalar ^ 0` being `1`). -/
theorem realEqual_rankZero (hTate : RealArchimedeanTateStatement) (a : ℝˣ)
    (c c' cd cd' : RealCharacterData)
    (hpar : (cd.mul cd').parity = (c.mul c').parity)
    (hexp : (cd.mul cd').exponent = -(c.mul c').exponent)
    (D : RealQuotientMeasureData 0) {W W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ} {C C' : ℂ}
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℝ, ℂ)) :
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      (∀ s : ℂ, σ < s.re → Integrable (realEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (realEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
          (ArchimedeanLocal.dualFunction (0 + 1) W') (realFourierTransform a Φ) s)
          D.measure) ∧
      DifferentiableOn ℂ (realEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (realEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} ∧
      MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
      (∀ s : ℂ, σ < s.re → realEqualIntegral D W W' Φ s = M s) ∧
      (∀ s : ℂ, σ < s.re → realEqualDualIntegral a D W W' Φ s = Md s) ∧
      ∀ᶠ s in Filter.codiscrete ℂ,
        ((realPairLFactor [RealBlock.character c] [RealBlock.character c']).denominator s)⁻¹ *
            Md (1 - s) =
          (realPairEpsilon [RealBlock.character c] [RealBlock.character c'] a
            (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
          ((realPairLFactor [RealBlock.character cd] [RealBlock.character cd']).denominator
            (1 - s))⁻¹ * M s := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_measure_eq (D := D)
  obtain ⟨-, hExt, hFE, -⟩ := hTate
  have hc0 : 0 < NNReal.sqrt ‖(a : ℝ)‖₊ := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
  obtain ⟨Z, hZ, -⟩ := hExt (lineSchwartz Φ) (c.mul c').parity (c.mul c').exponent
  obtain ⟨g, hg, hgFE⟩ := hFE (lineSchwartz Φ) (c.mul c').parity (c.mul c').exponent a
    (NNReal.sqrt ‖(a : ℝ)‖₊) hc0
  obtain ⟨Y, hY, -⟩ := hExt g (c.mul c').parity (-(c.mul c').exponent)
  have hgf : (g : ℝ → ℂ) = tateFourier a (NNReal.sqrt ‖(a : ℝ)‖₊) (lineSchwartz Φ) := funext hg
  have hZmero : MeromorphicOn Z Set.univ := hZ.1.meromorphicOn
  have hYmero : MeromorphicOn Y Set.univ := hY.1.meromorphicOn
  have hZeq : ∀ s : ℂ, 0 < (s + (c.mul c').exponent).re →
      Z s = RealTate.zeta (lineSchwartz Φ) (c.mul c').parity (s + (c.mul c').exponent) :=
    fun s hs => hZ.2 s hs
  have hYeq : ∀ s : ℂ, 0 < (s + -(c.mul c').exponent).re →
      Y s = RealTate.zeta g (c.mul c').parity (s + -(c.mul c').exponent) :=
    fun s hs => hY.2 s hs
  have hM : realEqualIntegral D W W' Φ = fun s => (κ : ℂ) * (C * C' *
      RealTate.zeta (lineSchwartz Φ) (c.mul c').parity (s + (c.mul c').exponent)) :=
    funext (equalIntegral_eq c c' hκ hW hW' Φ)
  have hMd : realEqualDualIntegral a D W W' Φ = fun s => (κ : ℂ) * (C * C' *
      RealTate.zeta g (c.mul c').parity (s + -(c.mul c').exponent)) := by
    rw [hgf]
    exact funext (equalDualIntegral_eq c c' hκ hW hW' a Φ)
  have hσ : ∀ s : ℂ, |(c.mul c').exponent.re| < s.re →
      0 < (s + (c.mul c').exponent).re ∧ 0 < (s + -(c.mul c').exponent).re := by
    intro s hs
    rw [Complex.add_re, Complex.add_re, Complex.neg_re]
    have h1 := neg_abs_le (c.mul c').exponent.re
    have h2 := le_abs_self (c.mul c').exponent.re
    constructor <;> linarith
  refine ⟨|(c.mul c').exponent.re|, fun s => (κ : ℂ) * (C * C' * Z s),
    fun s => (κ : ℂ) * (C * C' * Y s), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact integrable_equalIntegrand c c' hκ0 hκ hW hW' Φ (hσ s hs).1
  · intro s hs
    exact integrable_dualIntegrand c c' hκ0 hκ hW hW' a Φ g hgf (hσ s hs).2
  · rw [hM]
    intro s hs
    have hd := RealTate.differentiableAt_zeta (lineSchwartz Φ) (c.mul c').parity (hσ s hs).1
    exact (((hd.comp s (differentiableAt_id.add_const _)).const_mul (C * C')).const_mul
      (κ : ℂ)).differentiableWithinAt
  · rw [hMd]
    intro s hs
    have hd := RealTate.differentiableAt_zeta g (c.mul c').parity (hσ s hs).2
    exact (((hd.comp s (differentiableAt_id.add_const _)).const_mul (C * C')).const_mul
      (κ : ℂ)).differentiableWithinAt
  · intro s _
    exact (MeromorphicAt.const _ s).fun_mul
      ((MeromorphicAt.const _ s).fun_mul (hZmero s trivial))
  · intro s _
    exact (MeromorphicAt.const _ s).fun_mul
      ((MeromorphicAt.const _ s).fun_mul (hYmero s trivial))
  · intro s hs
    simp only [hM, hZeq s (hσ s hs).1]
  · intro s hs
    simp only [hMd, hYeq s (hσ s hs).2]
  · rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
    intro s₀
    filter_upwards [hgFE Z Y hZ hY s₀,
      (gammaReal.shift ((c.mul c').exponent + ((c.mul c').parity.val : ℂ))).denominator_eventually_ne_zero s₀,
      (reflectedGamma (c.mul c').exponent ((c.mul c').parity.val : ℂ)).denominator_eventually_ne_zero s₀]
      with s hs hG hG'
    have hG1 : Complex.Gammaℝ (s + (c.mul c').exponent + ((c.mul c').parity.val : ℂ)) ≠ 0 := by
      have h : (Complex.Gammaℝ (s + ((c.mul c').exponent + ((c.mul c').parity.val : ℂ))))⁻¹ ≠ 0 :=
        hG
      rw [← add_assoc] at h
      exact fun h0 => h (by rw [h0, inv_zero])
    have hG2 : Complex.Gammaℝ (1 - s - (c.mul c').exponent + ((c.mul c').parity.val : ℂ)) ≠ 0 := by
      have h : (Complex.Gammaℝ (1 - s - (c.mul c').exponent + ((c.mul c').parity.val : ℂ)))⁻¹ ≠ 0 :=
        hG'
      exact fun h0 => h (by rw [h0, inv_zero])
    rw [realPairLFactor_character, realPairLFactor_character, hpar, hexp, inv_inv, inv_inv,
      realPairEpsilon_character,
      show s + ((c.mul c').exponent + ((c.mul c').parity.val : ℂ)) =
        s + (c.mul c').exponent + ((c.mul c').parity.val : ℂ) by ring,
      show 1 - s + (-(c.mul c').exponent + ((c.mul c').parity.val : ℂ)) =
        1 - s - (c.mul c').exponent + ((c.mul c').parity.val : ℂ) by ring]
    rw [div_eq_iff hG2] at hs
    rw [hs]
    field_simp

end Langlands.Global.RankinSelbergGlobal.RealRankZero

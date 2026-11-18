import Langlands.Global.RankinSelberg.ComplexRankZeroHaar
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction
import Langlands.LocalFactor.Archimedean.Statement
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-! # The rank-one complex local Rankin–Selberg functional equation, from Tate's theory

For `W = C · χ_c ∘ det` and `W' = C' · χ_{c'} ∘ det` on `GL₁(ℂ)`, the equal-rank local
integrals `Ψ(s; W, W', Φ)` and `Ψ(s; W̃, W̃', Φ̂)` are multiples of complex Tate zeta integrals
of the restriction of `Φ` to the line and of its Fourier transform. The local functional
equation of `ComplexLocalEqualFunctionalEquationStatement` at `r = 0` follows from
`ComplexArchimedeanTateStatement`. See the paired Markdown.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology Filter
open scoped NNReal ENNReal SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexRankZero

open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open ArchimedeanLocal

attribute [local instance] unitsMeasurable unitsBorel rankZeroGLMeasurable rankZeroGLBorel
  rankZeroNMeasurable rankZeroNBorel rankZeroQMeasurable rankZeroQBorel

local instance localUniqueFinZeroAddOne : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))

/-! ### Complex Tate zeta integrals -/

namespace ComplexTate

/-- The integrand `f(z) (z/|z|)^m |z|^(2(s+t)-2)` of the complex Tate zeta integral, as in
`ComplexArchimedeanTateStatement` (value `0` at `z = 0`). -/
def integrand (f : ℂ → ℂ) (m : ℤ) (t s z : ℂ) : ℂ :=
  if z = 0 then 0 else
    f z * (z / (‖z‖ : ℂ)) ^ m * (‖z‖ : ℂ) ^ (2 * (s + t) - 2)

/-- The complex Tate zeta integral, for twice Lebesgue measure on `ℂ`, as in
`ComplexArchimedeanTateStatement`. -/
def zeta (f : ℂ → ℂ) (m : ℤ) (t s : ℂ) : ℂ :=
  ∫ z, integrand f m t s z ∂((2 : ℝ≥0∞) • volume)

/-- `Z` is a meromorphic function in normal form on `ℂ` extending the zeta integral from the
half-plane `Re(s + t) > 0`, as in `ComplexArchimedeanTateStatement`. -/
def ExtendsIntegral (Z : ℂ → ℂ) (f : ℂ → ℂ) (m : ℤ) (t : ℂ) : Prop :=
  MeromorphicNFOn Z Set.univ ∧ ∀ s, 0 < (s + t).re → Z s = zeta f m t s

/-- The scaled Fourier transform of the complex Tate statement:
`y ↦ c ∫ exp(4π i Re(a z y)) f(z) d(2 · Lebesgue)(z)`. -/
def tateFourier (a : ℂ) (c : ℝ≥0) (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  (c : ℂ) * ∫ z, Complex.exp (4 * (Real.pi : ℂ) * Complex.I * ((a * z * y).re : ℂ)) * f z
    ∂((2 : ℝ≥0∞) • volume)

theorem integral_two_smul (F : ℂ → ℂ) :
    ∫ z, F z ∂((2 : ℝ≥0∞) • volume) = 2 * ∫ z, F z := by
  rw [integral_smul_measure, ENNReal.toReal_ofNat, Complex.real_smul]
  push_cast
  rfl

theorem norm_integrand {f : ℂ → ℂ} {m : ℤ} {t s z : ℂ} (hz : z ≠ 0) :
    ‖integrand f m t s z‖ = ‖f z‖ * ‖z‖ ^ (2 * (s + t).re - 2) := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [integrand, ite_eq_right_of_eq_false _ _ (eq_false hz), norm_mul, norm_mul, norm_zpow, norm_div, Complex.norm_real,
    norm_norm, div_self hpos.ne', one_zpow, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  congr 2
  simp

theorem rpow_le_add {x y a b : ℝ} (hx : 0 < x) (ha : a ≤ y) (hb : y ≤ b) :
    x ^ y ≤ x ^ a + x ^ b := by
  rcases le_total x 1 with h | h
  · have h1 := Real.rpow_le_rpow_of_exponent_ge hx h ha
    have h2 := Real.rpow_nonneg hx.le b
    linarith
  · have h1 := Real.rpow_le_rpow_of_exponent_le h hb
    have h2 := Real.rpow_nonneg hx.le a
    linarith

/-- Domination of the integrand on a vertical strip `a ≤ Re(s + t) ≤ b` by the integrands at
the real points `s + t = a` and `s + t = b`. -/
theorem norm_integrand_le {f : ℂ → ℂ} {m : ℤ} {t s : ℂ} {a b : ℝ} (ha : a ≤ (s + t).re)
    (hb : (s + t).re ≤ b) (z : ℂ) :
    ‖integrand f m t s z‖ ≤
      ‖integrand f m t ((a : ℂ) - t) z‖ + ‖integrand f m t ((b : ℂ) - t) z‖ := by
  by_cases hz : z = 0
  · simp [integrand, hz]
  · rw [norm_integrand hz, norm_integrand hz, norm_integrand hz]
    have hre : ∀ x : ℝ, ((x : ℂ) - t + t).re = x := fun x => by simp
    rw [hre, hre, ← mul_add]
    refine mul_le_mul_of_nonneg_left (rpow_le_add (norm_pos_iff.mpr hz) ?_ ?_) (norm_nonneg _)
    · linarith
    · linarith

theorem continuousAt_integrand (f : ℂ → ℂ) (m : ℤ) (t s₀ z : ℂ) :
    ContinuousAt (fun s => integrand f m t s z) s₀ := by
  by_cases hz : z = 0
  · simp only [integrand, hz, ↓reduceIte]
    exact continuousAt_const
  · simp only [integrand, hz, ↓reduceIte]
    have hne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hz).ne'
    have hc : Continuous fun s : ℂ => ((‖z‖ : ℝ) : ℂ) ^ (2 * (s + t) - 2) :=
      (by fun_prop : Continuous fun s : ℂ => 2 * (s + t) - 2).const_cpow (Or.inl hne)
    exact continuousAt_const.mul hc.continuousAt

variable {f : ℂ → ℂ} {m : ℤ} {t : ℂ}

/-- The zeta integral is continuous on `Re(s + t) > 0`, by dominated convergence. -/
theorem continuousAt_zeta
    (hint : ∀ s, 0 < (s + t).re → Integrable (integrand f m t s) ((2 : ℝ≥0∞) • volume))
    {s₀ : ℂ} (hs₀ : 0 < (s₀ + t).re) : ContinuousAt (zeta f m t) s₀ := by
  set a : ℝ := (s₀ + t).re / 2
  set b : ℝ := (s₀ + t).re + 1
  have ha : 0 < a := by positivity
  have hcont : ContinuousAt (fun s : ℂ => (s + t).re) s₀ := by fun_prop
  have hnhds : ∀ᶠ s in 𝓝 s₀, (s + t).re ∈ Set.Ioo a b :=
    hcont.eventually (Ioo_mem_nhds (by simp only [a]; linarith) (by simp only [b]; linarith))
  have hre : ∀ x : ℝ, 0 < x → 0 < ((x : ℂ) - t + t).re := fun x hx => by simpa using hx
  refine continuousAt_of_dominated
    (bound := fun z => ‖integrand f m t ((a : ℂ) - t) z‖ + ‖integrand f m t ((b : ℂ) - t) z‖)
    ?_ ?_ ?_ (ae_of_all _ fun z => continuousAt_integrand f m t s₀ z)
  · filter_upwards [hnhds] with s hs
    exact (hint s (ha.trans hs.1)).aestronglyMeasurable
  · filter_upwards [hnhds] with s hs
    exact ae_of_all _ (norm_integrand_le hs.1.le hs.2.le)
  · exact (hint _ (hre a ha)).norm.add (hint _ (hre b (by positivity))).norm

/-- The zeta integral is holomorphic on `Re(s + t) > 0`: it agrees there with a meromorphic
extension `Z`, which is continuous, hence analytic, at every such point. -/
theorem differentiableAt_zeta {Z : ℂ → ℂ} (hZ : ExtendsIntegral Z f m t)
    (hint : ∀ s, 0 < (s + t).re → Integrable (integrand f m t s) ((2 : ℝ≥0∞) • volume))
    {s₀ : ℂ} (hs₀ : 0 < (s₀ + t).re) : DifferentiableAt ℂ (zeta f m t) s₀ := by
  have hopen : IsOpen {s : ℂ | 0 < (s + t).re} :=
    isOpen_lt continuous_const (by fun_prop)
  have heq : Z =ᶠ[𝓝 s₀] zeta f m t := by
    filter_upwards [hopen.mem_nhds hs₀] with s hs using hZ.2 s hs
  have hZc : ContinuousAt Z s₀ := (continuousAt_zeta hint hs₀).congr heq.symm
  have hana : AnalyticAt ℂ Z s₀ := (hZ.1.meromorphicOn s₀ trivial).analyticAt hZc
  exact hana.differentiableAt.congr_of_eventuallyEq heq.symm

end ComplexTate

open ComplexTate

/-! ### The line restriction of a Schwartz function on `ℂ¹` -/

/-- The Schwartz function `z ↦ Φ(z)` on `ℂ` attached to `Φ` on `ℂ^1`. -/
def lineSchwartz (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.funUnique (Fin (0 + 1)) ℝ ℂ).symm Φ

theorem lineSchwartz_apply (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) (z : ℂ) :
    lineSchwartz Φ z = Φ (fun _ => z) := rfl

theorem complexFourierTransform_const (a : ℂˣ) (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) (y : ℂ) :
    complexFourierTransform a (Φ : (Fin (0 + 1) → ℂ) → ℂ) (fun _ => y) =
      tateFourier a ‖(a : ℂ)‖₊ (lineSchwartz Φ) y := by
  rw [complexFourierTransform, ArchimedeanLocal.fourierTransform, complexSelfDualMeasure,
    complexScaledMeasure_measure]
  have hmp := (measurePreserving_funUnique
    ((‖(a : ℂ)‖₊ * 2) • (volume : Measure ℂ)) (Fin (0 + 1))).symm
  refine (hmp.integral_comp' _).symm.trans ?_
  rw [integral_smul_nnreal_measure, tateFourier, integral_two_smul, NNReal.smul_def,
    Complex.real_smul]
  push_cast
  rw [mul_assoc]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  show Φ (fun _ => z) * (complexScaledCharacter a).complex (∑ _x : Fin 1, z * y) =
    Complex.exp (4 * (Real.pi : ℂ) * Complex.I * (((a : ℂ) * z * y).re : ℂ)) * lineSchwartz Φ z
  rw [Fin.sum_univ_one, Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    complexScaledCharacter_apply, Real.fourierChar_apply, Algebra.trace_complex_apply,
    lineSchwartz_apply, mul_comm]
  congr 2
  rw [← mul_assoc]
  push_cast
  ring_nf

/-! ### Evaluation at scalar matrices -/

theorem determinant_tateScalarEquiv (u : ℂˣ) :
    GeneralLinear.determinant (Langlands.GodementJacquet.tateScalarEquiv ℂ u) = u :=
  (Langlands.GodementJacquet.tateScalarEquiv ℂ).symm_apply_apply u

theorem det_val_tateScalarEquiv (u : ℂˣ) :
    Matrix.det (Langlands.GodementJacquet.tateScalarEquiv ℂ u).val = u := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact congrArg Units.val (determinant_tateScalarEquiv u)

theorem lastRow_tateScalarEquiv (u : ℂˣ) :
    lastRow (n := 0) (Langlands.GodementJacquet.tateScalarEquiv ℂ u) = fun _ => (u : ℂ) := by
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  change (Matrix.GeneralLinearGroup.scalar (Fin 1) u : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = u
  simp [Matrix.GeneralLinearGroup.coe_scalar]

theorem detPower_tateScalarEquiv (u : ℂˣ) (s : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs
        (Langlands.GodementJacquet.tateScalarEquiv ℂ u) s =
      ((‖(u : ℂ)‖ : ℝ) : ℂ) ^ (2 * s) := by
  have hpos : 0 < ‖(u : ℂ)‖ := norm_pos_iff.mpr u.ne_zero
  rw [ArchimedeanLocal.detPower, complexNormalizedAbs, det_val_tateScalarEquiv, Real.log_pow,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]
  congr 1
  push_cast
  ring

theorem dualFunction_apply (W : Langlands.GeneralLinear (0 + 1) ℂ → ℂ)
    (g : Langlands.GeneralLinear (0 + 1) ℂ) :
    ArchimedeanLocal.dualFunction (0 + 1) W g = W (GeneralLinear.inverseTranspose 1 ℂ g) := by
  rw [ArchimedeanLocal.dualFunction]
  congr 1
  rw [show GeneralLinear.weylLong (0 + 1) ℂ = 1 from
    Langlands.RankinSelberg.RankOneGammaTwist.weylLong_one, one_mul]

/-! ### Character algebra -/

/-- `|u|⁻² · χ_d(u) · v · |u|^(2s) = v · (u/|u|)^m · |u|^(2(s+t)-2)` for `d` of weight `m` and
exponent `t`. -/
theorem character_shift (d : ComplexCharacterData) (v : ℂ) (u : ℂˣ) (s : ℂ) :
    (((‖(u : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        ((d.character u : ℂ) * v * ((‖(u : ℂ)‖ : ℝ) : ℂ) ^ (2 * s)) =
      v * ((u : ℂ) / ((‖(u : ℂ)‖ : ℝ) : ℂ)) ^ d.weight *
        ((‖(u : ℂ)‖ : ℝ) : ℂ) ^ (2 * (s + d.exponent) - 2) := by
  have hne : ((‖(u : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr u.ne_zero).ne'
  rw [d.character_eq, show 2 * (s + d.exponent) - 2 = 2 * d.exponent + 2 * s - 2 by ring,
    Complex.cpow_sub _ _ hne, Complex.cpow_add _ _ hne, Complex.cpow_two]
  push_cast
  rw [div_eq_mul_inv]
  ring

theorem mul_character_apply (c c' : ComplexCharacterData) (u : ℂˣ) :
    ((c.mul c').character u : ℂ) = (c.character u : ℂ) * (c'.character u : ℂ) := rfl

theorem inv_mul_character_apply (c c' : ComplexCharacterData) (u : ℂˣ) :
    ((c.mul c').inv.character u : ℂ) = (c.character u : ℂ)⁻¹ * (c'.character u : ℂ)⁻¹ := by
  rw [ComplexCharacterData.inv_character_apply, mul_character_apply, mul_inv]

theorem character_inv_apply (c : ComplexCharacterData) (u : ℂˣ) :
    (c.character u⁻¹ : ℂ) = (c.character u : ℂ)⁻¹ := by
  rw [map_inv, Units.val_inv_eq_inv_val]

/-! ### The integrands on the line -/

section Integrands

variable (c c' : ComplexCharacterData) {W W' : Langlands.GeneralLinear (0 + 1) ℂ → ℂ} {C C' : ℂ}

/-- The integrand of `Ψ(s; W, W', Φ)`, transported to `ℂ` and multiplied by `|z|⁻²`, is a
multiple of the complex Tate integrand of the line restriction of `Φ`. -/
theorem extend_equalIntegrand
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) (s : ℂ) (z : ℂ) :
    (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) * unitsExtend (complexEqualIntegrand W W' Φ s) z =
      C * C' * integrand (lineSchwartz Φ) (c.mul c').weight (c.mul c').exponent s z := by
  by_cases hz : z = 0
  · simp [hz, unitsExtend, integrand]
  · have hu : z = (Units.mk0 z hz : ℂ) := rfl
    rw [hu, unitsExtend_val]
    set u := Units.mk0 z hz
    simp only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, quotientUnits_symm_out]
    rw [hW, hW', determinant_tateScalarEquiv, lastRow_tateScalarEquiv,
      detPower_tateScalarEquiv, integrand, ite_eq_right_of_eq_false _ _ (eq_false u.ne_zero), lineSchwartz_apply]
    have h := character_shift (c.mul c') (Φ (fun _ => (u : ℂ))) u s
    rw [← h, mul_character_apply]
    ring

/-- The integrand of `Ψ(s; W̃, W̃', Φ̂)`, transported to `ℂ` and multiplied by `|z|⁻²`, is a
multiple of the complex Tate integrand, with weight `-m` and exponent `-t`, of the scaled
Fourier transform of the line restriction. -/
theorem extend_dualIntegrand
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (a : ℂˣ) (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) (s : ℂ) (z : ℂ) :
    (((‖z‖ ^ 2)⁻¹ : ℝ) : ℂ) *
        unitsExtend (complexEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
          (ArchimedeanLocal.dualFunction (0 + 1) W') (complexFourierTransform a Φ) s) z =
      C * C' * integrand (tateFourier a ‖(a : ℂ)‖₊ (lineSchwartz Φ))
        (-(c.mul c').weight) (-(c.mul c').exponent) s z := by
  by_cases hz : z = 0
  · simp [hz, unitsExtend, integrand]
  · have hu : z = (Units.mk0 z hz : ℂ) := rfl
    rw [hu, unitsExtend_val]
    set u := Units.mk0 z hz
    simp only [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, quotientUnits_symm_out,
      dualFunction_apply]
    rw [hW, hW', Langlands.RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose,
      determinant_tateScalarEquiv, lastRow_tateScalarEquiv, complexFourierTransform_const,
      detPower_tateScalarEquiv, integrand, ite_eq_right_of_eq_false _ _ (eq_false u.ne_zero), character_inv_apply,
      character_inv_apply]
    have h := character_shift (c.mul c').inv
      (tateFourier a ‖(a : ℂ)‖₊ (lineSchwartz Φ) u) u s
    rw [ComplexCharacterData.inv_weight, ComplexCharacterData.inv_exponent] at h
    rw [← h, inv_mul_character_apply]
    ring

variable {D : ComplexQuotientMeasureData 0} {κ : ℝ≥0}

theorem equalIntegral_eq (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) (s : ℂ) :
    complexEqualIntegral D W W' Φ s = (κ : ℂ) / 2 * (C * C') *
      zeta (lineSchwartz Φ) (c.mul c').weight (c.mul c').exponent s := by
  change ∫ q, complexEqualIntegrand W W' Φ s q ∂D.measure = _
  rw [integral_eq hκ, zeta, integral_two_smul,
    integral_congr_ae (ae_of_all _ fun z => extend_equalIntegrand c c' hW hW' Φ s z),
    integral_const_mul]
  ring

theorem equalDualIntegral_eq (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (a : ℂˣ) (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) (s : ℂ) :
    complexEqualDualIntegral a D W W' Φ s = (κ : ℂ) / 2 * (C * C') *
      zeta (tateFourier a ‖(a : ℂ)‖₊ (lineSchwartz Φ)) (-(c.mul c').weight)
        (-(c.mul c').exponent) s := by
  change ∫ q, complexEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
    (ArchimedeanLocal.dualFunction (0 + 1) W') (complexFourierTransform a Φ) s q
      ∂D.measure = _
  rw [integral_eq hκ, zeta, integral_two_smul,
    integral_congr_ae (ae_of_all _ fun z => extend_dualIntegrand c c' hW hW' a Φ s z),
    integral_const_mul]
  ring

theorem integrable_equalIntegrand (hκ0 : κ ≠ 0)
    (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) {s : ℂ}
    (hint : Integrable (integrand (lineSchwartz Φ) (c.mul c').weight (c.mul c').exponent s)
      ((2 : ℝ≥0∞) • volume)) :
    Integrable (complexEqualIntegrand W W' Φ s) D.measure :=
  (integrable_iff hκ0 hκ _).mpr
    ((((integrable_smul_measure two_ne_zero ENNReal.ofNat_ne_top).mp hint).const_mul
      (C * C')).congr (ae_of_all _ fun z => (extend_equalIntegrand c c' hW hW' Φ s z).symm))

theorem integrable_dualIntegrand (hκ0 : κ ≠ 0)
    (hκ : D.measure = κ • unitsHaar.map quotientUnits.symm)
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (a : ℂˣ) (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) {s : ℂ}
    (hint : Integrable (integrand (tateFourier a ‖(a : ℂ)‖₊ (lineSchwartz Φ))
      (-(c.mul c').weight) (-(c.mul c').exponent) s) ((2 : ℝ≥0∞) • volume)) :
    Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
      (ArchimedeanLocal.dualFunction (0 + 1) W') (complexFourierTransform a Φ) s)
      D.measure :=
  (integrable_iff hκ0 hκ _).mpr
    ((((integrable_smul_measure two_ne_zero ENNReal.ofNat_ne_top).mp hint).const_mul
      (C * C')).congr (ae_of_all _ fun z => (extend_dualIntegrand c c' hW hW' a Φ s z).symm))

end Integrands

/-! ### Rank-one factors -/

theorem complexPairBlocks_singleton (c c' : ComplexCharacterData) :
    complexPairBlocks [c] [c'] = [c.mul c'] := rfl

theorem complexPairLFactor_singleton (c c' : ComplexCharacterData) (s : ℂ) :
    (complexPairLFactor [c] [c']).denominator s =
      (Complex.Gammaℂ (s + ((c.mul c').exponent +
        ((c.mul c').weight.natAbs : ℂ) / 2)))⁻¹ := by
  rw [complexPairLFactor, complexPairBlocks_singleton, complexLFactor_singleton]
  rfl

theorem inv_mul_exponent (c c' : ComplexCharacterData) :
    (c.inv.mul c'.inv).exponent = -(c.mul c').exponent := by
  show -c.exponent + -c'.exponent = -(c.exponent + c'.exponent)
  ring

theorem inv_mul_weight_natAbs (c c' : ComplexCharacterData) :
    (c.inv.mul c'.inv).weight.natAbs = (c.mul c').weight.natAbs := by
  show (-c.weight + -c'.weight).natAbs = (c.weight + c'.weight).natAbs
  rw [← neg_add, Int.natAbs_neg]

theorem complexPairEpsilon_singleton (c c' : ComplexCharacterData) (a : ℂˣ) (c0 : ℝ≥0)
    (hc : 0 < c0) (s : ℂ) :
    (complexPairEpsilon [c] [c'] a c0 hc s : ℂ) =
      (c0 : ℂ) * ((a : ℂ) / ((‖(a : ℂ)‖ : ℝ) : ℂ)) ^ (c.mul c').weight *
        ((‖(a : ℂ)‖ : ℝ) : ℂ) ^ (2 * (s + (c.mul c').exponent - 1)) *
        Complex.I ^ (c.mul c').weight.natAbs := by
  rw [complexPairEpsilon, complexPairBlocks_singleton, complexEpsilon_singleton,
    ComplexCharacterData.coe_epsilon, (c.mul c').character_eq]
  have hne : ((‖(a : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr a.ne_zero).ne'
  rw [show 2 * (s + (c.mul c').exponent - 1) = 2 * (c.mul c').exponent + 2 * (s - 1) by ring,
    Complex.cpow_add _ _ hne]
  ring

/-- The entire function `s ↦ Γℂ(1 - s - t + q)⁻¹`. -/
def reflectedGammaComplex (t q : ℂ) : ReciprocalEntire where
  denominator := fun s => (Complex.Gammaℂ (1 - s - t + q))⁻¹
  entire := by
    have h : Differentiable ℂ (fun s : ℂ => 1 - s - t + q) := by fun_prop
    exact Complex.differentiable_Gammaℂ_inv.comp h
  nonzero := ⟨q - t, by rw [show 1 - (q - t) - t + q = 1 by ring]; simp [Real.pi_ne_zero]⟩

/-! ### The rank-one local functional equation -/

/-- **The complex local functional equation at `r = 0`.** If `W = C · χ_c ∘ det` and
`W' = C' · χ_{c'} ∘ det` on `GL₁(ℂ)`, then the conclusion of
`ComplexLocalEqualFunctionalEquationStatement` holds for `d = [c]`, `d' = [c']`, assuming the
complex Tate theory `ComplexArchimedeanTateStatement`. -/
theorem complexEqual_rankZero (hTate : ComplexArchimedeanTateStatement) (a : ℂˣ)
    (c c' : ComplexCharacterData) (D : ComplexQuotientMeasureData 0)
    {W W' : Langlands.GeneralLinear (0 + 1) ℂ → ℂ} {C C' : ℂ}
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (hW' : ∀ g, W' g = C' * (c'.character (GeneralLinear.determinant g) : ℂ))
    (Φ : 𝓢(Fin (0 + 1) → ℂ, ℂ)) :
    ∃ (σ : ℝ) (M Md : ℂ → ℂ),
      (∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand W W' Φ s) D.measure) ∧
      (∀ s : ℂ, σ < s.re →
        Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (0 + 1) W)
          (ArchimedeanLocal.dualFunction (0 + 1) W') (complexFourierTransform a Φ) s)
          D.measure) ∧
      DifferentiableOn ℂ (complexEqualIntegral D W W' Φ) {s : ℂ | σ < s.re} ∧
      DifferentiableOn ℂ (complexEqualDualIntegral a D W W' Φ) {s : ℂ | σ < s.re} ∧
      MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
      (∀ s : ℂ, σ < s.re → complexEqualIntegral D W W' Φ s = M s) ∧
      (∀ s : ℂ, σ < s.re → complexEqualDualIntegral a D W W' Φ s = Md s) ∧
      ∀ᶠ s in Filter.codiscrete ℂ,
        ((complexPairLFactor [c] [c']).denominator s)⁻¹ * Md (1 - s) =
          complexCentralSign [c'] ^ 0 *
            (complexPairEpsilon [c] [c'] a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
            ((complexPairLFactor ([c].map ComplexCharacterData.inv)
              ([c'].map ComplexCharacterData.inv)).denominator (1 - s))⁻¹ * M s := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_measure_eq D
  obtain ⟨hInt, hExt, hFE, -⟩ := hTate
  set m : ℤ := (c.mul c').weight with hm
  set t : ℂ := (c.mul c').exponent with ht
  have hc0 : 0 < ‖(a : ℂ)‖₊ := nnnorm_pos.mpr a.ne_zero
  obtain ⟨Z, hZ, -⟩ := hExt (lineSchwartz Φ) m t
  obtain ⟨g, hg, hgFE⟩ := hFE (lineSchwartz Φ) m t a ‖(a : ℂ)‖₊ hc0
  obtain ⟨Y, hY, -⟩ := hExt g (-m) (-t)
  have hZ' : ExtendsIntegral Z (lineSchwartz Φ) m t := hZ
  have hY' : ExtendsIntegral Y g (-m) (-t) := hY
  have hgf : (g : ℂ → ℂ) = tateFourier a ‖(a : ℂ)‖₊ (lineSchwartz Φ) := funext hg
  have hIntZ : ∀ s, 0 < (s + t).re →
      Integrable (integrand (lineSchwartz Φ) m t s) ((2 : ℝ≥0∞) • volume) :=
    fun s hs => hInt (lineSchwartz Φ) m t s hs
  have hIntY : ∀ s, 0 < (s + -t).re →
      Integrable (integrand g (-m) (-t) s) ((2 : ℝ≥0∞) • volume) :=
    fun s hs => hInt g (-m) (-t) s hs
  set K : ℂ := (κ : ℂ) / 2 * (C * C') with hK
  have hM : complexEqualIntegral D W W' Φ = fun s => K * zeta (lineSchwartz Φ) m t s :=
    funext (equalIntegral_eq c c' hκ hW hW' Φ)
  have hMd : complexEqualDualIntegral a D W W' Φ = fun s => K * zeta g (-m) (-t) s := by
    rw [hgf]
    exact funext (equalDualIntegral_eq c c' hκ hW hW' a Φ)
  have hσ : ∀ s : ℂ, |t.re| < s.re → 0 < (s + t).re ∧ 0 < (s + -t).re := by
    intro s hs
    rw [Complex.add_re, Complex.add_re, Complex.neg_re]
    have h1 := neg_abs_le t.re
    have h2 := le_abs_self t.re
    constructor <;> linarith
  refine ⟨|t.re|, fun s => K * Z s, fun s => K * Y s, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact integrable_equalIntegrand c c' hκ0 hκ hW hW' Φ (hIntZ s (hσ s hs).1)
  · intro s hs
    have h := hIntY s (hσ s hs).2
    rw [hgf] at h
    exact integrable_dualIntegrand c c' hκ0 hκ hW hW' a Φ h
  · rw [hM]
    intro s hs
    exact ((differentiableAt_zeta hZ' hIntZ (hσ s hs).1).const_mul K).differentiableWithinAt
  · rw [hMd]
    intro s hs
    exact ((differentiableAt_zeta hY' hIntY (hσ s hs).2).const_mul K).differentiableWithinAt
  · intro s _
    exact (MeromorphicAt.const _ s).fun_mul (hZ.1.meromorphicOn s trivial)
  · intro s _
    exact (MeromorphicAt.const _ s).fun_mul (hY.1.meromorphicOn s trivial)
  · intro s hs
    simp only [hM, hZ'.2 s (hσ s hs).1]
  · intro s hs
    simp only [hMd, hY'.2 s (hσ s hs).2]
  · rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
    intro s₀
    filter_upwards [hgFE Z Y hZ hY s₀,
      (gammaComplex.shift (t + (m.natAbs : ℂ) / 2)).denominator_eventually_ne_zero s₀,
      (reflectedGammaComplex t ((m.natAbs : ℂ) / 2)).denominator_eventually_ne_zero s₀]
      with s hs hG hG'
    have hG1 : Complex.Gammaℂ (s + t + (m.natAbs : ℂ) / 2) ≠ 0 := by
      have h : (Complex.Gammaℂ (s + (t + (m.natAbs : ℂ) / 2)))⁻¹ ≠ 0 := hG
      rw [← add_assoc] at h
      exact fun h0 => h (by rw [h0, inv_zero])
    have hG2 : Complex.Gammaℂ (1 - s - t + (m.natAbs : ℂ) / 2) ≠ 0 := by
      have h : (Complex.Gammaℂ (1 - s - t + (m.natAbs : ℂ) / 2))⁻¹ ≠ 0 := hG'
      exact fun h0 => h (by rw [h0, inv_zero])
    have hL1 := complexPairLFactor_singleton c c' s
    have hL2 := complexPairLFactor_singleton c.inv c'.inv (1 - s)
    rw [inv_mul_exponent, inv_mul_weight_natAbs] at hL2
    have hε := complexPairEpsilon_singleton c c' a ‖(a : ℂ)‖₊ hc0 s
    rw [← hm, ← ht] at hε hL1 hL2
    simp only [List.map_cons, List.map_nil]
    rw [hL1, hL2, hε, inv_inv, inv_inv, pow_zero, one_mul,
      show s + (t + (m.natAbs : ℂ) / 2) = s + t + (m.natAbs : ℂ) / 2 by ring,
      show 1 - s + (-t + (m.natAbs : ℂ) / 2) = 1 - s - t + (m.natAbs : ℂ) / 2 by ring]
    rw [div_eq_iff hG2] at hs
    rw [hs]
    generalize Complex.Gammaℂ (s + t + (m.natAbs : ℂ) / 2) = G1 at hG1 ⊢
    generalize Complex.Gammaℂ (1 - s - t + (m.natAbs : ℂ) / 2) = G2 at hG2 ⊢
    field_simp

end Langlands.Global.RankinSelbergGlobal.ComplexRankZero

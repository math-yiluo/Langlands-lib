import Langlands.Global.Hecke.MixedSpaceFourier
import Langlands.Global.Factors.HeckeFunctionalEquationStatement

/-! # Archimedean zeta integrals and epsilon factors of actual Hecke characters -/

noncomputable section

open MeasureTheory Complex NumberField NumberField.InfinitePlace
open scoped Classical Real

namespace Langlands.LocalFactor.Archimedean

/-- A complex exponential `y ↦ exp (y w)` which is identically one on the real line forces
`w = 0`. -/
theorem eq_zero_of_forall_cexp_mul_eq_one {w : ℂ}
    (h : ∀ y : ℝ, Complex.exp ((y : ℂ) * w) = 1) : w = 0 := by
  have h1 : HasDerivAt (fun y : ℝ => Complex.exp (((id y : ℝ) : ℂ) * w))
      (Complex.exp (((id (0 : ℝ) : ℝ) : ℂ) * w) * (((1 : ℝ) : ℂ) * w)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).cexp
  have hconst : (fun y : ℝ => Complex.exp (((id y : ℝ) : ℂ) * w)) = fun _ => 1 :=
    funext fun y => h y
  rw [hconst] at h1
  have := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using this

/-- A complex power of a positive real exponential. -/
theorem ofReal_exp_cpow (y : ℝ) (t : ℂ) :
    ((Real.exp y : ℝ) : ℂ) ^ t = Complex.exp ((y : ℂ) * t) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne'),
    ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]

namespace RealCharacterData

/-- Two presented real characters which are mutually inverse have equal parities and
opposite exponents. -/
theorem parity_eq_and_exponent_eq_neg_of_inv (d d' : RealCharacterData)
    (h : ∀ x : ℝˣ, d'.character x = (d.character x)⁻¹) :
    d'.parity = d.parity ∧ d'.exponent = -d.exponent := by
  have hc : ∀ x : ℝˣ, (d'.character x : ℂ) * (d.character x : ℂ) = 1 := fun x => by
    rw [h x, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]
  constructor
  · have h1 := hc (-1)
    rw [d'.character_eq, d.character_eq] at h1
    simp only [Units.val_neg, Units.val_one, abs_neg, abs_one, div_one, ofReal_neg,
      ofReal_one, one_cpow, mul_one] at h1
    generalize d'.parity = a at h1 ⊢
    generalize d.parity = b at h1 ⊢
    fin_cases a <;> fin_cases b <;> first | rfl | (norm_num at h1)
  · have hw : ∀ y : ℝ, Complex.exp ((y : ℂ) * (d'.exponent + d.exponent)) = 1 := fun y => by
      have h1 := hc (Units.mk0 (Real.exp y) (Real.exp_pos y).ne')
      rw [d'.character_eq, d.character_eq, Units.val_mk0, abs_of_pos (Real.exp_pos y),
        div_self (Real.exp_pos y).ne', ofReal_one, one_pow, one_pow, one_mul, one_mul,
        ofReal_exp_cpow, ofReal_exp_cpow, ← Complex.exp_add, ← mul_add] at h1
      exact h1
    have := eq_zero_of_forall_cexp_mul_eq_one hw
    linear_combination this

end RealCharacterData

namespace ComplexCharacterData

/-- Two presented complex characters which are mutually inverse have opposite weights and
opposite exponents. -/
theorem weight_eq_neg_and_exponent_eq_neg_of_inv (d d' : ComplexCharacterData)
    (h : ∀ z : Langlands.Weil.Archimedean.ComplexWeil, d'.character z = (d.character z)⁻¹) :
    d'.weight = -d.weight ∧ d'.exponent = -d.exponent := by
  have hc : ∀ z : Langlands.Weil.Archimedean.ComplexWeil,
      (d'.character z : ℂ) * (d.character z : ℂ) = 1 := fun z => by
    rw [h z, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _)]
  constructor
  · have hw : ∀ y : ℝ, Complex.exp ((y : ℂ) * (I * ((d'.weight : ℂ) + d.weight))) = 1 :=
      fun y => by
        have h1 := hc (Units.mk0 (Complex.exp (y * I)) (Complex.exp_ne_zero _))
        rw [d'.character_eq, d.character_eq, Units.val_mk0, Complex.norm_exp_ofReal_mul_I,
          ofReal_one, div_one, one_cpow, one_cpow, mul_one, mul_one,
          ← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add] at h1
        rw [← h1]
        congr 1
        ring
    have h0 := eq_zero_of_forall_cexp_mul_eq_one hw
    have h2 : ((d'.weight + d.weight : ℤ) : ℂ) = 0 := by
      push_cast
      exact (mul_eq_zero.mp h0).resolve_left I_ne_zero
    have h3 : d'.weight + d.weight = 0 := by exact_mod_cast h2
    omega
  · have hw : ∀ y : ℝ, Complex.exp ((y : ℂ) * (2 * d'.exponent + 2 * d.exponent)) = 1 :=
      fun y => by
        have h1 := hc (Units.mk0 ((Real.exp y : ℝ) : ℂ)
          (by exact_mod_cast (Real.exp_pos y).ne'))
        rw [d'.character_eq, d.character_eq, Units.val_mk0,
          Complex.norm_of_nonneg (Real.exp_pos y).le,
          div_self (by exact_mod_cast (Real.exp_pos y).ne'), one_zpow, one_zpow, one_mul,
          one_mul, ofReal_exp_cpow, ofReal_exp_cpow, ← Complex.exp_add, ← mul_add] at h1
        exact h1
    have := eq_zero_of_forall_cexp_mul_eq_one hw
    linear_combination this / 2

end ComplexCharacterData

end Langlands.LocalFactor.Archimedean

namespace Langlands.Global.HeckeFunctionalEquation

open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- At a real place, the presentation of the inverse Hecke character presents the
inverse character. -/
theorem realCharacter_inv_of_presentation (χ : HeckeCharacter K) {v : InfinitePlace K}
    (hv : v.IsReal) {d d' : RealCharacterData}
    (h : IsRealCharacterPresentation hv (χ.infiniteComponent v) d)
    (h' : IsRealCharacterPresentation hv (χ⁻¹.infiniteComponent v) d') (x : ℝˣ) :
    d'.character x = (d.character x)⁻¹ := by
  have hx : Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMonoidHom
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm.toMonoidHom x) =
        x := by
    ext
    simp
  rw [← hx, h' _, h _, HeckeCharacter.infiniteComponent_inv]
  rfl

/-- At a complex place, the presentation of the inverse Hecke character presents the
inverse character. -/
theorem complexCharacter_inv_of_presentation (χ : HeckeCharacter K) {v : InfinitePlace K}
    (hv : v.IsComplex) {d d' : ComplexCharacterData}
    (h : IsComplexCharacterPresentation hv (χ.infiniteComponent v) d)
    (h' : IsComplexCharacterPresentation hv (χ⁻¹.infiniteComponent v) d')
    (x : Langlands.Weil.Archimedean.ComplexWeil) :
    d'.character x = (d.character x)⁻¹ := by
  have hx : Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).toMonoidHom
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm.toMonoidHom
        x) = x := by
    ext
    simp
  rw [← hx, h' _, h _, HeckeCharacter.infiniteComponent_inv]
  rfl

/-- The explicit entire archimedean ratio of the Gaussian zeta integral to the archimedean
L-factor. -/
def archimedeanZetaRatio (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData) (s : ℂ) : ℂ :=
  (∏ v, ((|(aR v : ℝ)| : ℝ) : ℂ) ^ (-(s + (dR v).exponent + (((dR v).parity : ℕ) : ℂ)) / 2)) *
    ∏ v, (π / 2 : ℂ) * ((‖((aC v : ℂˣ) : ℂ)‖ : ℝ) : ℂ) ^
      (-(s + (dC v).exponent + ((dC v).weight.natAbs : ℂ) / 2))

theorem differentiable_archimedeanZetaRatio (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData) :
    Differentiable ℂ (archimedeanZetaRatio aR aC dR dC) := by
  unfold archimedeanZetaRatio
  refine Differentiable.mul ?_ ?_
  · refine Differentiable.fun_finsetProd fun v _ => ?_
    have h0 : (((|(aR v : ℝ)| : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast abs_ne_zero.mpr (aR v).ne_zero
    exact Differentiable.const_cpow (by fun_prop) (.inl h0)
  · refine Differentiable.fun_finsetProd fun v _ => ?_
    have h0 : (((‖((aC v : ℂˣ) : ℂ)‖ : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr (aC v).ne_zero
    exact (Differentiable.const_cpow (by fun_prop) (.inl h0)).const_mul _

theorem archimedeanZetaRatio_ne_zero (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData) (s : ℂ) :
    archimedeanZetaRatio aR aC dR dC s ≠ 0 := by
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => ?_)
    (Finset.prod_ne_zero_iff.mpr fun v _ => ?_)
  · exact Complex.cpow_ne_zero_iff.mpr
      (.inl (by exact_mod_cast abs_ne_zero.mpr (aR v).ne_zero))
  · refine mul_ne_zero (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) two_ne_zero) ?_
    exact Complex.cpow_ne_zero_iff.mpr
      (.inl (by exact_mod_cast norm_ne_zero_iff.mpr (aC v).ne_zero))

private theorem gammaℂ_ne_zero {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  exact Complex.cpow_ne_zero_iff.mpr
    (.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)))

/-- The Gaussian zeta integral of a presented product character, times the archimedean
L-factor denominators, is the explicit archimedean ratio. -/
theorem integral_mul_infiniteDenominator (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (dR : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (dC : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData) (s : ℂ)
    (hR : ∀ v, 0 < (s + (dR v).exponent + (((dR v).parity : ℕ) : ℂ)).re)
    (hC : ∀ v, 0 < (s + (dC v).exponent + ((dC v).weight.natAbs : ℂ) / 2).re) :
    (∫ x : mixedEmbedding.mixedSpace K,
        Hecke.mixedGaussian (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
            (fun v => (dR v).parity) (fun v => (dC v).weight) x *
          Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
            (fun v => (dC v).weight) (fun v => (dC v).exponent) x *
          ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (s - 1)) *
        ((∏ v, (dR v).lFactor.denominator s) * ∏ v, (dC v).lFactor.denominator s) =
      archimedeanZetaRatio aR aC dR dC s := by
  rw [Hecke.integral_mixedGaussian_mul_mixedCharFun
    (haR := fun v => by exact_mod_cast (aR v).ne_zero) (haC := fun v => (aC v).ne_zero)
    (hR := hR) (hC := hC)]
  have hRd : ∀ v, (dR v).lFactor.denominator s =
      (Gammaℝ (s + (dR v).exponent + (((dR v).parity : ℕ) : ℂ)))⁻¹ := fun v => by
    show (Gammaℝ (s + ((dR v).exponent + (((dR v).parity : ℕ) : ℂ))))⁻¹ = _
    rw [add_assoc]
  have hCd : ∀ v, (dC v).lFactor.denominator s =
      (Gammaℂ (s + (dC v).exponent + ((dC v).weight.natAbs : ℂ) / 2))⁻¹ := fun v => by
    show (Gammaℂ (s + ((dC v).exponent + ((dC v).weight.natAbs : ℂ) / 2)))⁻¹ = _
    rw [add_assoc]
  simp only [hRd, hCd]
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    archimedeanZetaRatio]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [mul_inv_cancel_right₀ (Complex.Gammaℝ_ne_zero_of_re_pos (hR v))]
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [mul_inv_cancel_right₀ (gammaℂ_ne_zero (hC v))]

private theorem real_place (a : ℝˣ) (d : RealCharacterData) (s : ℂ) :
    ((Real.sqrt |(a : ℝ)| : ℝ) : ℂ) *
        ((((Real.sqrt |(a : ℝ)|)⁻¹ : ℝ) : ℂ) *
          (I * (((a : ℝ) / |(a : ℝ)| : ℝ) : ℂ)) ^ (d.parity : ℕ)) *
        ((|(a : ℝ)| : ℝ) : ℂ) ^ (-(1 - s + -d.exponent + ((d.parity : ℕ) : ℂ)) / 2) =
      (d.epsilon a (NNReal.sqrt ‖(a : ℝ)‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) s : ℂ) *
        ((|(a : ℝ)| : ℝ) : ℂ) ^ (-(s + d.exponent + ((d.parity : ℕ) : ℂ)) / 2) := by
  have hr : (0 : ℝ) < |(a : ℝ)| := abs_pos.mpr a.ne_zero
  have hr0 : (((|(a : ℝ)| : ℝ)) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hs0 : ((Real.sqrt |(a : ℝ)| : ℝ) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hr).ne'
  have hsq : ((Real.sqrt |(a : ℝ)| : ℝ) : ℂ) = (((|(a : ℝ)| : ℝ)) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
    norm_num
  rw [RealCharacterData.coe_epsilon, d.character_eq, Real.coe_sqrt, coe_nnnorm,
    Real.norm_eq_abs, ofReal_inv, mul_inv_cancel_left₀ hs0, mul_pow, hsq,
    show -(1 - s + -d.exponent + ((d.parity : ℕ) : ℂ)) / 2 =
      1 / 2 + d.exponent + (s - 1) + -(s + d.exponent + ((d.parity : ℕ) : ℂ)) / 2 by ring,
    cpow_add _ _ hr0, cpow_add _ _ hr0, cpow_add _ _ hr0]
  ring

private theorem complex_place (a : ℂˣ) (d : ComplexCharacterData) (s : ℂ) :
    (((2 * ‖(a : ℂ)‖ : ℝ)) : ℂ) *
        ((((2 * ‖(a : ℂ)‖)⁻¹ : ℝ) : ℂ) *
          (I ^ d.weight.natAbs * ((a : ℂ) / ((‖(a : ℂ)‖ : ℝ) : ℂ)) ^ d.weight)) *
        ((π / 2 : ℂ) * ((‖(a : ℂ)‖ : ℝ) : ℂ) ^
          (-(1 - s + -d.exponent + ((-d.weight).natAbs : ℂ) / 2))) =
      (d.epsilon a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
        ((π / 2 : ℂ) * ((‖(a : ℂ)‖ : ℝ) : ℂ) ^
          (-(s + d.exponent + (d.weight.natAbs : ℂ) / 2))) := by
  have hρ : (0 : ℝ) < ‖(a : ℂ)‖ := norm_pos_iff.mpr a.ne_zero
  have hρ0 : (((‖(a : ℂ)‖ : ℝ)) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hρ.ne'
  have h2 : (((2 * ‖(a : ℂ)‖ : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos two_pos hρ).ne'
  rw [ComplexCharacterData.coe_epsilon, d.character_eq, coe_nnnorm, Int.natAbs_neg, ofReal_inv,
    mul_inv_cancel_left₀ h2,
    show -(1 - s + -d.exponent + (d.weight.natAbs : ℂ) / 2) =
      1 + 2 * d.exponent + 2 * (s - 1) + -(s + d.exponent + (d.weight.natAbs : ℂ) / 2) by ring,
    cpow_add _ _ hρ0, cpow_add _ _ hρ0, cpow_add _ _ hρ0, cpow_one]
  ring

/-- The archimedean local functional equation for the explicit ratios: the Fourier constants
of the product Gaussian times the dual ratio at `1 - s` are the archimedean epsilon factor
times the ratio at `s`, when the dual data are the inverse parameters. -/
theorem mixedGaussianConst_mul_archimedeanZetaRatio_one_sub
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (dR dR' : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (dC dC' : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hp : ∀ v, (dR' v).parity = (dR v).parity) (ht : ∀ v, (dR' v).exponent = -(dR v).exponent)
    (hN : ∀ v, (dC' v).weight = -(dC v).weight)
    (hu : ∀ v, (dC' v).exponent = -(dC v).exponent) (s : ℂ) :
    (Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ)) : ℂ) *
        Hecke.mixedGaussianFTConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
          (fun v => (dR v).parity) (fun v => (dC v).weight) *
        archimedeanZetaRatio aR aC dR' dC' (1 - s) =
      ((∏ v, ((dR v).epsilon (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
        ∏ v, ((dC v).epsilon (aC v) ‖((aC v : ℂ))‖₊
          (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)) *
        archimedeanZetaRatio aR aC dR dC s := by
  rw [Hecke.mixedGaussianConst, Hecke.mixedGaussianFTConst, archimedeanZetaRatio,
    archimedeanZetaRatio, ofReal_mul, ofReal_prod, ofReal_prod]
  simp only [hp, ht, hN, hu]
  rw [show ∀ a b c d e f : ℂ, a * b * (c * d) * (e * f) = a * c * e * (b * d * f) by
    intros; ring]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  congr 1
  · exact Finset.prod_congr rfl fun v _ => real_place (aR v) (dR v) s
  · exact Finset.prod_congr rfl fun v _ => complex_place (aC v) (dC v) s

private theorem re_pos_of_norm_le {s t w : ℂ} {σ : ℝ} (hw : 0 ≤ w.re) (ht : ‖t‖ ≤ σ)
    (hs : σ < s.re) : 0 < (s + t + w).re := by
  have := (abs_le.mp ((Complex.abs_re_le_norm t).trans ht)).1
  simp only [add_re]
  linarith

/-- **Archimedean zeta integrals and epsilon factors.** For an actual Hecke character with
real and complex presentations of its infinite components and of those of its inverse, and
nonzero additive scales, the Gaussian zeta integrals of the character and of its inverse
(against the Gaussian of opposite complex weights), times the archimedean L-factor
denominators, are entire nowhere-vanishing functions on a right half-plane, and the
Fourier constants of the Gaussian relate them through the archimedean epsilon factor. -/
theorem exists_archimedeanZeta (χ : HeckeCharacter K)
    (aR : {v : InfinitePlace K // v.IsReal} → ℝˣ)
    (aC : {v : InfinitePlace K // v.IsComplex} → ℂˣ)
    (dR dR' : {v : InfinitePlace K // v.IsReal} → RealCharacterData)
    (hR : ∀ v, IsRealCharacterPresentation v.2 (χ.infiniteComponent v.1) (dR v))
    (hR' : ∀ v, IsRealCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dR' v))
    (dC dC' : {v : InfinitePlace K // v.IsComplex} → ComplexCharacterData)
    (hC : ∀ v, IsComplexCharacterPresentation v.2 (χ.infiniteComponent v.1) (dC v))
    (hC' : ∀ v, IsComplexCharacterPresentation v.2 (χ⁻¹.infiniteComponent v.1) (dC' v)) :
    ∃ (E E' : ℂ → ℂ) (σ₀ : ℝ), Differentiable ℂ E ∧ Differentiable ℂ E' ∧
      (∀ s, E s ≠ 0) ∧ (∀ s, E' s ≠ 0) ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∫ x : mixedEmbedding.mixedSpace K,
            Hecke.mixedGaussian (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
                (fun v => (dR v).parity) (fun v => (dC v).weight) x *
              Hecke.mixedCharFun (fun v => (dR v).parity) (fun v => (dR v).exponent)
                (fun v => (dC v).weight) (fun v => (dC v).exponent) x *
              ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (s - 1)) *
            ((∏ v, (dR v).lFactor.denominator s) * ∏ v, (dC v).lFactor.denominator s) =
          E s) ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∫ x : mixedEmbedding.mixedSpace K,
            Hecke.mixedGaussian (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
                (fun v => (dR v).parity) (-(fun v => (dC v).weight)) x *
              Hecke.mixedCharFun (fun v => (dR' v).parity) (fun v => (dR' v).exponent)
                (fun v => (dC' v).weight) (fun v => (dC' v).exponent) x *
              ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (s - 1)) *
            ((∏ v, (dR' v).lFactor.denominator s) * ∏ v, (dC' v).lFactor.denominator s) =
          E' s) ∧
      ∀ s : ℂ,
        (Hecke.mixedGaussianConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ)) : ℂ) *
            Hecke.mixedGaussianFTConst (fun v => (aR v : ℝ)) (fun v => ((aC v : ℂˣ) : ℂ))
              (fun v => (dR v).parity) (fun v => (dC v).weight) * E' (1 - s) =
          ((∏ v, ((dR v).epsilon (aR v) (NNReal.sqrt ‖((aR v : ℝ))‖₊)
              (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (aR v).ne_zero)) s : ℂ)) *
            ∏ v, ((dC v).epsilon (aC v) ‖((aC v : ℂ))‖₊
              (nnnorm_pos.mpr (aC v).ne_zero) s : ℂ)) * E s := by
  have hRel : ∀ v, (dR' v).parity = (dR v).parity ∧ (dR' v).exponent = -(dR v).exponent :=
    fun v => RealCharacterData.parity_eq_and_exponent_eq_neg_of_inv _ _
      (realCharacter_inv_of_presentation χ v.2 (hR v) (hR' v))
  have hCel : ∀ v, (dC' v).weight = -(dC v).weight ∧ (dC' v).exponent = -(dC v).exponent :=
    fun v => ComplexCharacterData.weight_eq_neg_and_exponent_eq_neg_of_inv _ _
      (complexCharacter_inv_of_presentation χ v.2 (hC v) (hC' v))
  let σ₀ : ℝ := (∑ v, ‖(dR v).exponent‖ + ∑ v, ‖(dC v).exponent‖) +
    (∑ v, ‖(dR' v).exponent‖ + ∑ v, ‖(dC' v).exponent‖)
  have h1 : ∀ v, ‖(dR v).exponent‖ ≤ σ₀ := fun v => by
    have := Finset.single_le_sum (f := fun v => ‖(dR v).exponent‖)
      (fun v _ => norm_nonneg _) (Finset.mem_univ v)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dC v).exponent)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dR' v).exponent)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dC' v).exponent)
    simp only [σ₀]
    linarith
  have h2 : ∀ v, ‖(dC v).exponent‖ ≤ σ₀ := fun v => by
    have := Finset.single_le_sum (f := fun v => ‖(dC v).exponent‖)
      (fun v _ => norm_nonneg _) (Finset.mem_univ v)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dR v).exponent)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dR' v).exponent)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dC' v).exponent)
    simp only [σ₀]
    linarith
  have h3 : ∀ v, ‖(dR' v).exponent‖ ≤ σ₀ := fun v => by
    have := Finset.single_le_sum (f := fun v => ‖(dR' v).exponent‖)
      (fun v _ => norm_nonneg _) (Finset.mem_univ v)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dR v).exponent)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dC v).exponent)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dC' v).exponent)
    simp only [σ₀]
    linarith
  have h4 : ∀ v, ‖(dC' v).exponent‖ ≤ σ₀ := fun v => by
    have := Finset.single_le_sum (f := fun v => ‖(dC' v).exponent‖)
      (fun v _ => norm_nonneg _) (Finset.mem_univ v)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dR v).exponent)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dC v).exponent)
    have := Finset.sum_nonneg (s := Finset.univ) (fun v _ => norm_nonneg (dR' v).exponent)
    simp only [σ₀]
    linarith
  have hnat : ∀ n : ℕ, 0 ≤ ((n : ℂ)).re := fun n => by simp
  have hnat2 : ∀ n : ℕ, 0 ≤ ((n : ℂ) / 2).re := fun n => by
    rw [Complex.div_ofNat_re]
    simp only [natCast_re]
    positivity
  refine ⟨archimedeanZetaRatio aR aC dR dC, archimedeanZetaRatio aR aC dR' dC', σ₀,
    differentiable_archimedeanZetaRatio _ _ _ _, differentiable_archimedeanZetaRatio _ _ _ _,
    archimedeanZetaRatio_ne_zero _ _ _ _, archimedeanZetaRatio_ne_zero _ _ _ _,
    fun s hs => ?_, fun s hs => ?_, fun s => ?_⟩
  · exact integral_mul_infiniteDenominator aR aC dR dC s
      (fun v => re_pos_of_norm_le (hnat _) (h1 v) hs)
      (fun v => re_pos_of_norm_le (hnat2 _) (h2 v) hs)
  · have hpf : (fun v => (dR v).parity) = fun v => (dR' v).parity :=
      funext fun v => (hRel v).1.symm
    have hNf : (-(fun v : {v : InfinitePlace K // v.IsComplex} => (dC v).weight)) =
        fun v => (dC' v).weight :=
      funext fun v => by rw [Pi.neg_apply, (hCel v).1]
    rw [hpf, hNf]
    exact integral_mul_infiniteDenominator aR aC dR' dC' s
      (fun v => re_pos_of_norm_le (hnat _) (h3 v) hs)
      (fun v => re_pos_of_norm_le (hnat2 _) (h4 v) hs)
  · exact mixedGaussianConst_mul_archimedeanZetaRatio_one_sub aR aC dR dR' dC dC'
      (fun v => (hRel v).1) (fun v => (hRel v).2) (fun v => (hCel v).1) (fun v => (hCel v).2) s

end Langlands.Global.HeckeFunctionalEquation

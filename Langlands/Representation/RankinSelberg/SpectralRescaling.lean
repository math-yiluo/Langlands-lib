import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.RationalZeta

/-! # Spectral rescaling of rational continuations and Laurent generators -/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

/-- Substitution of a nonzero scalar multiple of the polynomial variable. -/
def polynomialRescale (c : ℂˣ) : ℂ[X] ≃ₐ[ℂ] ℂ[X] :=
  Polynomial.algEquivOfCompEqX (C (c : ℂ) * X) (C (↑c⁻¹ : ℂ) * X)
    (by simp [← mul_assoc, ← C_mul]) (by simp [← mul_assoc, ← C_mul])

@[simp] theorem polynomialRescale_apply (c : ℂˣ) (P : ℂ[X]) :
    polynomialRescale c P = P.comp (C (c : ℂ) * X) := by
  simp [polynomialRescale, ← comp_eq_aeval]

@[simp] theorem polynomialRescale_symm (c : ℂˣ) :
    (polynomialRescale c).symm = polynomialRescale c⁻¹ := by
  simp [polynomialRescale]

/-- The complex algebra automorphism `R(X) ↦ R(c X)` of rational functions. -/
def rationalRescale (c : ℂˣ) : RationalFunctions ≃ₐ[ℂ] RationalFunctions :=
  IsFractionRing.algEquivOfAlgEquiv (polynomialRescale c)

@[simp] theorem rationalRescale_algebraMap (c : ℂˣ) (P : ℂ[X]) :
    rationalRescale c (algebraMap ℂ[X] RationalFunctions P) =
      algebraMap ℂ[X] RationalFunctions (P.comp (C (c : ℂ) * X)) := by
  simp [rationalRescale]

@[simp] theorem rationalRescale_symm (c : ℂˣ) :
    (rationalRescale c).symm = rationalRescale c⁻¹ := by
  simp [rationalRescale]

@[simp] theorem rationalRescale_inv_apply (c : ℂˣ) (R : RationalFunctions) :
    rationalRescale c⁻¹ (rationalRescale c R) = R := by
  rw [← rationalRescale_symm, AlgEquiv.symm_apply_apply]

@[simp] theorem rationalRescale_apply_inv (c : ℂˣ) (R : RationalFunctions) :
    rationalRescale c (rationalRescale c⁻¹ R) = R := by
  rw [← rationalRescale_symm, AlgEquiv.apply_symm_apply]

@[simp] theorem rationalRescale_C (c : ℂˣ) (a : ℂ) :
    rationalRescale c (RatFunc.C a) = RatFunc.C a :=
  (rationalRescale c).commutes a

@[simp] theorem rationalRescale_X (c : ℂˣ) :
    rationalRescale c RatFunc.X = RatFunc.C (c : ℂ) * RatFunc.X := by
  simpa using rationalRescale_algebraMap c X

/-- A displayed fraction for the rescaled function, before reducing it. -/
theorem rationalRescale_num_div_denom (c : ℂˣ) (R : RationalFunctions) :
    rationalRescale c R =
      algebraMap ℂ[X] RationalFunctions (R.num.comp (C (c : ℂ) * X)) /
      algebraMap ℂ[X] RationalFunctions (R.denom.comp (C (c : ℂ) * X)) := by
  rw [← rationalRescale_algebraMap, ← rationalRescale_algebraMap, ← map_div₀,
    RatFunc.num_div_denom]

/-- Reduction can only remove factors from the substituted denominator. -/
theorem rationalRescale_denom_dvd (c : ℂˣ) (R : RationalFunctions) :
    (rationalRescale c R).denom ∣ R.denom.comp (C (c : ℂ) * X) := by
  rw [rationalRescale_num_div_denom]
  exact RatFunc.denom_div_dvd _ _

/-- Nonvanishing is preserved at the corresponding evaluation point. -/
theorem rationalRescale_denom_ne_zero (c : ℂˣ) (R : RationalFunctions) (x : ℂ)
    (h : R.denom.eval ((c : ℂ) * x) ≠ 0) :
    (rationalRescale c R).denom.eval x ≠ 0 := by
  intro hz
  have he := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) x
    (rationalRescale_denom_dvd c R) hz
  exact h (by simpa using he)

/-- The reduced denominators vanish at exactly corresponding points. -/
theorem rationalRescale_denom_ne_zero_iff (c : ℂˣ) (R : RationalFunctions) (x : ℂ) :
    (rationalRescale c R).denom.eval x ≠ 0 ↔ R.denom.eval ((c : ℂ) * x) ≠ 0 := by
  refine ⟨fun h => ?_, rationalRescale_denom_ne_zero c R x⟩
  have h' := rationalRescale_denom_ne_zero c⁻¹ (rationalRescale c R)
    ((c : ℂ) * x) (by simpa [← mul_assoc] using h)
  simpa using h'

/-- Rational evaluation agrees with substitution away from the denominator. -/
theorem rationalRescale_eval (c : ℂˣ) (R : RationalFunctions) (x : ℂ)
    (h : R.denom.eval ((c : ℂ) * x) ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) x (rationalRescale c R) =
      RatFunc.eval (RingHom.id ℂ) ((c : ℂ) * x) R := by
  have hden : R.denom.comp (C (c : ℂ) * X) ≠ 0 := by
    simpa only [polynomialRescale_apply, zero_comp] using
      (polynomialRescale c).injective.ne (RatFunc.denom_ne_zero R)
  have he := (RatFunc.num_mul_eq_mul_denom_iff (x := rationalRescale c R) hden).2
    (rationalRescale_num_div_denom c R)
  have heval := congrArg (fun P : ℂ[X] => P.eval x) he
  have hd := rationalRescale_denom_ne_zero c R x h
  apply (div_eq_div_iff hd h).2
  simpa only [eval_mul, eval_comp, eval_C, eval_X, eval₂_id] using heval

/-- Substitution preserves the actual embedded Laurent coefficient ring. -/
theorem rationalRescale_laurentToRatFunc (c : ℂˣ) (a : LaurentCoefficients) :
    ∃ b : LaurentCoefficients, laurentToRatFunc b = rationalRescale c (laurentToRatFunc a) := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' + b', by simp only [map_add, ha', hb']⟩
  | C_mul_T n a =>
    refine ⟨LaurentPolynomial.C (a * (c : ℂ) ^ n) * LaurentPolynomial.T n, ?_⟩
    have hC (z : ℂ) : laurentToRatFunc (LaurentPolynomial.C z) = RatFunc.C z := by
      simp [laurentToRatFunc]
    simp only [map_mul, hC, laurentToRatFunc_T, rationalRescale_C,
      map_zpow₀, rationalRescale_X, mul_zpow, mul_assoc]

/-- Transport of membership in the genuine Laurent span. -/
theorem rationalRescale_mem_zetaSpan (c : ℂˣ) {S : Set RationalFunctions}
    {R : RationalFunctions} (h : R ∈ zetaSpan S) :
    rationalRescale c R ∈ zetaSpan ((rationalRescale c) '' S) := by
  induction h using Submodule.span_induction with
  | mem R hR => exact mem_zetaSpan ⟨R, hR, rfl⟩
  | zero => simpa only [map_zero] using (zetaSpan ((rationalRescale c) '' S)).zero_mem
  | add R T _ _ hR hT => simpa only [map_add] using Submodule.add_mem _ hR hT
  | smul a R _ hR =>
    obtain ⟨b, hb⟩ := rationalRescale_laurentToRatFunc c a
    have h := (zetaSpan ((rationalRescale c) '' S)).smul_mem b hR
    simpa only [Algebra.smul_def, algebraMap_laurent, hb, map_mul] using h

/-- Rescaling is a bijection on the genuine Laurent spans. -/
theorem rationalRescale_mem_zetaSpan_iff (c : ℂˣ) (S : Set RationalFunctions)
    (R : RationalFunctions) :
    rationalRescale c R ∈ zetaSpan ((rationalRescale c) '' S) ↔ R ∈ zetaSpan S := by
  refine ⟨fun h => ?_, rationalRescale_mem_zetaSpan c⟩
  have h' := rationalRescale_mem_zetaSpan c⁻¹ h
  have himg : rationalRescale c⁻¹ '' (rationalRescale c '' S) = S := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨rationalRescale c x, ⟨x, hx, rfl⟩, rationalRescale_inv_apply c x⟩
  simpa only [himg, rationalRescale_inv_apply] using h'

/-- A normalized reciprocal-polynomial generator transports under substitution. -/
theorem IsNormalizedGenerator.rescale {S : Set RationalFunctions} {P : ℂ[X]}
    (h : IsNormalizedGenerator S P) (c : ℂˣ) :
    IsNormalizedGenerator ((rationalRescale c) '' S) (P.comp (C (c : ℂ) * X)) := by
  apply (isNormalizedGenerator_iff _ _).2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero, eval_comp, eval_mul, eval_C, eval_X, mul_zero]
      using h.1
  · rintro _ ⟨R, hR, rfl⟩
    obtain ⟨a, ha⟩ := h.clearsDenominators (mem_zetaSpan hR)
    obtain ⟨b, hb⟩ := rationalRescale_laurentToRatFunc c a
    exact ⟨b, by rw [hb, ha, map_mul, rationalRescale_algebraMap]⟩
  · have hmem : (algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈ zetaSpan S := by
      rw [h.2]
      exact Submodule.mem_span_singleton_self _
    simpa only [map_inv₀, rationalRescale_algebraMap] using
      rationalRescale_mem_zetaSpan c hmem

/-- The nonzero complex scalar implementing a shift of the spectral parameter. -/
def spectralShiftUnit (q : ℕ) (hq : 1 < q) (u : ℂ) : ℂˣ :=
  Units.mk0 (spectralPoint q u) (Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq)))))

@[simp] theorem coe_spectralShiftUnit (q : ℕ) (hq : 1 < q) (u : ℂ) :
    (spectralShiftUnit q hq u : ℂ) = spectralPoint q u := rfl

/-- Translation becomes multiplication of the spectral points. -/
theorem spectralPoint_add {q : ℕ} (hq : 1 < q) (s u : ℂ) :
    spectralPoint q (s + u) = spectralPoint q u * spectralPoint q s := by
  rw [spectralPoint, neg_add, Complex.cpow_add]
  · exact mul_comm _ _
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq))

@[simp] theorem spectralShiftUnit_neg (q : ℕ) (hq : 1 < q) (u : ℂ) :
    spectralShiftUnit q hq (-u) = (spectralShiftUnit q hq u)⁻¹ := by
  apply Units.ext
  simp [spectralPoint, Complex.cpow_neg]

/-- Shift any rational continuation, including its denominator condition. -/
theorem HasRationalContinuation.shift {q : ℕ} (hq : 1 < q)
    {f : ℂ → ℂ} {R : RationalFunctions} (h : HasRationalContinuation q f R) (u : ℂ) :
    HasRationalContinuation q (fun s => f (s + u))
      (rationalRescale (spectralShiftUnit q hq u) R) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a - u.re, fun s hs => ?_⟩
  obtain ⟨hd, he⟩ := ha (s + u) (by simp only [Complex.add_re]; linarith)
  rw [spectralPoint_add hq] at hd he
  exact ⟨rationalRescale_denom_ne_zero _ _ _ hd,
    he.trans (rationalRescale_eval (spectralShiftUnit q hq u) R _ hd).symm⟩

/-- The shift construction gives both directions for arbitrary functions. -/
theorem hasRationalContinuation_shift_iff {q : ℕ} (hq : 1 < q)
    (f : ℂ → ℂ) (R : RationalFunctions) (u : ℂ) :
    HasRationalContinuation q (fun s => f (s + u))
      (rationalRescale (spectralShiftUnit q hq u) R) ↔ HasRationalContinuation q f R := by
  refine ⟨fun h => ?_, fun h => h.shift hq u⟩
  simpa only [spectralShiftUnit_neg, rationalRescale_inv_apply, neg_add_cancel_right]
    using h.shift hq (-u)

end Langlands.RankinSelberg

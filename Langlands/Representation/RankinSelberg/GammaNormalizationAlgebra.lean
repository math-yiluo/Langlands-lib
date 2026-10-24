import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.LaurentTransport

/-! Normalization of a rational gamma equation by the normalized generators of
the two value sets it relates. The reflection `X ↦ q⁻¹/X` carries Laurent
coefficients to Laurent coefficients, so the incidence of the two value sets
identifies their generated modules after reflection and multiplication by the
gamma factor. The normalized generators then differ by a Laurent unit, which is
a nonzero monomial. -/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial LocalFactor

namespace GammaNormalization

/-- Reflection `X ↦ δ/X` of the image of a Laurent polynomial is again such an image. -/
theorem exists_laurent_subst (δ : ℂˣ) (a : LaurentCoefficients) :
    ∃ b : LaurentCoefficients,
      laurentToRatFunc b = RationalReflection.subst δ (laurentToRatFunc a) := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    exact ⟨a' + b', by rw [map_add, map_add, map_add, ha', hb']⟩
  | C_mul_T n a =>
    refine ⟨LaurentPolynomial.C (a * (δ : ℂ) ^ n) * LaurentPolynomial.T (-n), ?_⟩
    have hsC : ∀ z : ℂ, RationalReflection.subst δ (RatFunc.C z) = RatFunc.C z :=
      fun z => (RationalReflection.subst δ).commutes z
    simp only [map_mul, map_zpow₀, laurentToRatFunc_C, laurentToRatFunc_T, hsC,
      RationalReflection.subst_X, RationalReflection.reflectedVariable,
      RatFunc.algebraMap_eq_C]
    rw [div_zpow, zpow_neg]
    ring

/-- The gamma equation on its pointwise domain is an identity of rational functions. -/
theorem rational_identity_of_gammaFunctionalEquation {q : ℕ} (hq : 1 < q) {δ : ℂˣ}
    (hδ : (δ : ℂ) = (q : ℂ)⁻¹) {ζ : ℂˣ} {e : ℕ} {G R Rdual : RationalFunctions}
    (h : GammaFunctionalEquation q ζ e G R Rdual) :
    RationalReflection.subst δ Rdual = RatFunc.C ((ζ : ℂ) ^ e) * (G * R) := by
  let A := RationalReflection.subst δ Rdual
  let B := RatFunc.C ((ζ : ℂ) ^ e) * (G * R)
  let bad : Set ℝ := {t | R.denom.eval (spectralPoint q t) = 0} ∪
    {t | Rdual.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0} ∪
    {t | G.denom.eval (spectralPoint q t) = 0}
  have hbad : bad.Finite :=
    ((finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R)).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rdual))).union
      (finite_spectralPoint_roots hq (RatFunc.denom_ne_zero G))
  have hU : ((fun t : ℝ => spectralPoint q t) '' badᶜ).Infinite :=
    hbad.infinite_compl.image (spectralPoint_ofReal_injective hq).injOn
  have hsign : ∀ z : ℂ, RationalEvaluation.RegularAt (RatFunc.C ((ζ : ℂ) ^ e)) z := by
    intro z
    simpa using (RationalEvaluation.RegularAt.polynomial (z := z) (C ((ζ : ℂ) ^ e)))
  have hpoint : ∀ t ∈ badᶜ,
      RationalEvaluation.RegularAt A (spectralPoint q t) ∧
      RationalEvaluation.RegularAt B (spectralPoint q t) ∧
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) A =
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) B := by
    intro t ht
    simp only [bad, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
    obtain ⟨⟨hR, hRd⟩, hG⟩ := ht
    have href : (δ : ℂ) / spectralPoint q t = spectralPoint q (1 - (t : ℂ)) := by
      rw [hδ, spectralPoint_one_sub hq]
    have hz := spectralPoint_ne_zero hq (t : ℂ)
    have hRd' : RationalEvaluation.RegularAt Rdual ((δ : ℂ) / spectralPoint q t) := by
      rw [href]; exact hRd
    refine ⟨RationalEvaluation.regular_subst δ hz hRd',
      (hsign _).mul ((show RationalEvaluation.RegularAt G _ from hG).mul hR), ?_⟩
    change RatFunc.eval (RingHom.id ℂ) (spectralPoint q t)
      (RationalReflection.subst δ Rdual) = RatFunc.eval (RingHom.id ℂ) (spectralPoint q t)
        (RatFunc.C ((ζ : ℂ) ^ e) * (G * R))
    rw [RationalEvaluation.eval_subst δ hz hRd', href,
      RationalEvaluation.eval_mul (hsign _) ((show RationalEvaluation.RegularAt G _ from hG).mul hR),
      RationalEvaluation.eval_mul hG hR, RatFunc.eval_C]
    exact h t hR hRd hG
  apply rationalFunction_eq_of_infinite_eval_eq A B _ hU
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).1
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).2.1
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).2.2

/-- A unit of the Laurent coefficient ring is a nonzero monomial. -/
theorem exists_monomial_of_mul_eq_one {a b : LaurentCoefficients} (h : a * b = 1) :
    ∃ (c : ℂˣ) (m : ℤ), a = LaurentPolynomial.C (c : ℂ) * LaurentPolynomial.T m := by
  obtain ⟨k, A, hA⟩ := LaurentPolynomial.exists_T_pow a
  obtain ⟨l, B, hB⟩ := LaurentPolynomial.exists_T_pow b
  have hAB : A * B = X ^ (k + l) := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hA, hB, Polynomial.toLaurent_X_pow]
    calc a * LaurentPolynomial.T k * (b * LaurentPolynomial.T l)
        = (a * b) * (LaurentPolynomial.T k * LaurentPolynomial.T l) := by ring
      _ = LaurentPolynomial.T ((k + l : ℕ) : ℤ) := by
        rw [h, one_mul, ← LaurentPolynomial.T_add]; push_cast; rfl
  obtain ⟨i, -, u, hu⟩ := (dvd_prime_pow Polynomial.prime_X (k + l)).mp ⟨B, hAB.symm⟩
  obtain ⟨r, hr, hrC⟩ := Polynomial.isUnit_iff.mp (u⁻¹).isUnit
  have hA' : A = C r * X ^ i := by
    rw [hrC, ← hu, mul_comm A, ← mul_assoc, Units.inv_mul, one_mul]
  have ha : a = Polynomial.toLaurent A * LaurentPolynomial.T (-(k : ℤ)) := by
    rw [hA, mul_assoc, ← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero,
      mul_one]
  refine ⟨hr.unit, (i : ℤ) - k, ?_⟩
  rw [ha, hA', map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow, mul_assoc,
    ← LaurentPolynomial.T_add, IsUnit.unit_spec, sub_eq_add_neg]

variable {q : ℕ} {δ ζ : ℂˣ} {e : ℕ} {G : RationalFunctions} {S T : Set RationalFunctions}

/-- First incidence: reflection of `ζ^e G f` lies in the dual module for every `f`
in the original module. -/
theorem subst_mem_zetaSpan (hq : 1 < q) (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hST : ∀ R ∈ S, ∃ Rdual ∈ T, GammaFunctionalEquation q ζ e G R Rdual)
    {f : RationalFunctions} (hf : f ∈ zetaSpan S) :
    RationalReflection.subst δ (RatFunc.C ((ζ : ℂ) ^ e) * (G * f)) ∈ zetaSpan T := by
  induction hf using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨Rdual, hRd, h⟩ := hST R hR
    rw [← rational_identity_of_gammaFunctionalEquation hq hδ h,
      RationalReflection.subst_subst]
    exact mem_zetaSpan hRd
  | zero => simp only [mul_zero, map_zero]; exact (zetaSpan T).zero_mem
  | add f g _ _ hf hg =>
    rw [mul_add, mul_add, map_add]
    exact add_mem hf hg
  | smul a f _ hf =>
    obtain ⟨b, hb⟩ := exists_laurent_subst δ a
    have he : RationalReflection.subst δ (RatFunc.C ((ζ : ℂ) ^ e) * (G * (a • f))) =
        b • RationalReflection.subst δ (RatFunc.C ((ζ : ℂ) ^ e) * (G * f)) := by
      rw [Algebra.smul_def, Algebra.smul_def, algebraMap_laurent, algebraMap_laurent, hb,
        ← map_mul]
      congr 1
      ring
    rw [he]
    exact Submodule.smul_mem _ b hf

/-- Second incidence: reflection of every element of the dual module is `ζ^e G g`
for some `g` in the original module. -/
theorem exists_subst_eq_mul (hq : 1 < q) (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hTS : ∀ Rdual ∈ T, ∃ R ∈ S, GammaFunctionalEquation q ζ e G R Rdual)
    {f : RationalFunctions} (hf : f ∈ zetaSpan T) :
    ∃ g ∈ zetaSpan S,
      RationalReflection.subst δ f = RatFunc.C ((ζ : ℂ) ^ e) * (G * g) := by
  induction hf using Submodule.span_induction with
  | mem Rdual hRd =>
    obtain ⟨R, hR, h⟩ := hTS Rdual hRd
    exact ⟨R, mem_zetaSpan hR, rational_identity_of_gammaFunctionalEquation hq hδ h⟩
  | zero => exact ⟨0, (zetaSpan S).zero_mem, by simp⟩
  | add f f' _ _ hf hf' =>
    obtain ⟨g, hg, hfg⟩ := hf
    obtain ⟨g', hg', hfg'⟩ := hf'
    exact ⟨g + g', add_mem hg hg', by rw [map_add, hfg, hfg']; ring⟩
  | smul a f _ hf =>
    obtain ⟨g, hg, hfg⟩ := hf
    obtain ⟨b, hb⟩ := exists_laurent_subst δ a
    refine ⟨b • g, Submodule.smul_mem _ b hg, ?_⟩
    rw [Algebra.smul_def, Algebra.smul_def, algebraMap_laurent, algebraMap_laurent, map_mul,
      ← hb, hfg]
    ring

/-- Clearing the two nonzero denominators in `L / S = Z (G / P)`. -/
theorem mul_eq_of_mul_inv_eq {K : Type*} [Field K] {Z G S P L : K} (hP : P ≠ 0)
    (hS : S ≠ 0) (h : L * S⁻¹ = Z * (G * P⁻¹)) : Z * G * S = L * P := by
  calc Z * G * S = Z * G * S * (P⁻¹ * P) := by rw [inv_mul_cancel₀ hP, mul_one]
    _ = Z * (G * P⁻¹) * (P * S) := by ring
    _ = L * S⁻¹ * (P * S) := by rw [h]
    _ = L * P * (S⁻¹ * S) := by ring
    _ = L * P := by rw [inv_mul_cancel₀ hS, mul_one]

/-- Clearing the two nonzero denominators in `1 / S = Z (G (D / P))`. -/
theorem eq_mul_of_inv_eq {K : Type*} [Field K] {Z G S P D : K} (hP : P ≠ 0)
    (hS : S ≠ 0) (h : S⁻¹ = Z * (G * (D * P⁻¹))) : P = D * (Z * G * S) := by
  calc P = S⁻¹ * (S * P) := by rw [← mul_assoc, inv_mul_cancel₀ hS, one_mul]
    _ = Z * (G * (D * P⁻¹)) * (S * P) := by rw [h]
    _ = D * (Z * G * S) * (P⁻¹ * P) := by ring
    _ = D * (Z * G * S) := by rw [inv_mul_cancel₀ hP, mul_one]

/-- If `Y = L P` and `P = D Y` with `P ≠ 0`, then `L D = 1`. -/
theorem mul_eq_one_of_cycle {K : Type*} [Field K] {Y L D P : K} (hP : P ≠ 0)
    (h1 : Y = L * P) (h2 : P = D * Y) : L * D = 1 := by
  apply mul_right_cancel₀ hP
  rw [one_mul]
  linear_combination (-1 : K) * h2 - D * h1

/-- Evaluation of the image of a polynomial is polynomial evaluation. -/
theorem eval_algebraMap_polynomial (A : ℂ[X]) (z : ℂ) :
    RatFunc.eval (RingHom.id ℂ) z (algebraMap ℂ[X] RationalFunctions A) = A.eval z := by
  rw [RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id]

end GammaNormalization

open GammaNormalization in
/-- Algebraic normalization of a rational gamma equation by the normalized
generators of the two value sets it relates in both directions. -/
theorem gammaNormalization_of_incidence {q : ℕ} (hq : 1 < q) (ζ : ℂˣ) (e : ℕ)
    (G : RationalFunctions) (S T : Set RationalFunctions) (P Pdual : ℂ[X])
    (hP : IsNormalizedGenerator S P) (hPd : IsNormalizedGenerator T Pdual)
    (hST : ∀ R ∈ S, ∃ Rdual ∈ T, GammaFunctionalEquation q ζ e G R Rdual)
    (hTS : ∀ Rdual ∈ T, ∃ R ∈ S, GammaFunctionalEquation q ζ e G R Rdual) :
    ∃ (c : ℂˣ) (m : ℤ), ∀ R Rdual : RationalFunctions,
      GammaFunctionalEquation q ζ e G R Rdual →
        NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let δ : ℂˣ := Units.mk0 (q : ℂ)⁻¹ (inv_ne_zero hq0)
  have hδ : (δ : ℂ) = (q : ℂ)⁻¹ := rfl
  have hP0 : algebraMap ℂ[X] RationalFunctions P ≠ 0 :=
    RatFunc.algebraMap_ne_zero hP.polynomial_ne_zero
  have hPd0 : algebraMap ℂ[X] RationalFunctions Pdual ≠ 0 :=
    RatFunc.algebraMap_ne_zero hPd.polynomial_ne_zero
  have hsPd0 : RationalReflection.subst δ (algebraMap ℂ[X] RationalFunctions Pdual) ≠ 0 := by
    intro h0
    apply hPd0
    simpa only [RationalReflection.subst_subst, map_zero] using
      congrArg (RationalReflection.subst δ) h0
  -- The first incidence gives `ζ^e G ρ(Pdual) = b' P` with `b'` Laurent.
  have h1 := subst_mem_zetaSpan hq hδ hST
    (f := (algebraMap ℂ[X] RationalFunctions P)⁻¹)
    (by rw [hP.2]; exact Submodule.mem_span_singleton_self _)
  rw [hPd.2] at h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h1
  obtain ⟨b', hb'⟩ := exists_laurent_subst δ b
  have hb2 := congrArg (RationalReflection.subst δ) hb
  rw [RationalReflection.subst_subst, Algebra.smul_def, algebraMap_laurent,
    map_mul (RationalReflection.subst δ), map_inv₀, ← hb'] at hb2
  have hstar := mul_eq_of_mul_inv_eq hP0 hsPd0 hb2
  -- The second incidence gives `P = d ζ^e G ρ(Pdual)` with `d` Laurent.
  obtain ⟨g, hg, hg'⟩ := exists_subst_eq_mul hq hδ hTS
    (f := (algebraMap ℂ[X] RationalFunctions Pdual)⁻¹)
    (by rw [hPd.2]; exact Submodule.mem_span_singleton_self _)
  rw [hP.2] at hg
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hg
  rw [← hd, Algebra.smul_def, algebraMap_laurent, map_inv₀] at hg'
  have hstar2 := eq_mul_of_inv_eq hP0 hsPd0 hg'
  -- Hence `b'` is a Laurent unit, that is, a nonzero monomial.
  have hbd : b' * d = 1 := by
    apply laurentToRatFunc_injective
    rw [map_mul, map_one]
    exact mul_eq_one_of_cycle hP0 hstar hstar2
  obtain ⟨c, m, hcm⟩ := exists_monomial_of_mul_eq_one hbd
  rw [hcm, map_mul laurentToRatFunc, laurentToRatFunc_C, laurentToRatFunc_T] at hstar
  refine ⟨(ζ ^ e)⁻¹ * c, m, fun R Rdual h s hR hRd => ?_⟩
  have hid := rational_identity_of_gammaFunctionalEquation hq hδ h
  have hprod : RationalReflection.subst δ (algebraMap ℂ[X] RationalFunctions Pdual * Rdual) =
      RatFunc.C (c : ℂ) * RatFunc.X ^ m * (algebraMap ℂ[X] RationalFunctions P * R) := by
    rw [map_mul (RationalReflection.subst δ), hid]
    linear_combination R * hstar
  -- Evaluate the rational identity at the spectral point.
  have hz := spectralPoint_ne_zero hq s
  have href : (δ : ℂ) / spectralPoint q s = spectralPoint q (1 - s) := by
    rw [hδ, spectralPoint_one_sub hq]
  have hRd' : RationalEvaluation.RegularAt Rdual ((δ : ℂ) / spectralPoint q s) := by
    rw [href]; exact hRd
  have hPdreg : RationalEvaluation.RegularAt (algebraMap ℂ[X] RationalFunctions Pdual)
      ((δ : ℂ) / spectralPoint q s) :=
    RationalEvaluation.RegularAt.polynomial Pdual
  have hPreg : RationalEvaluation.RegularAt (algebraMap ℂ[X] RationalFunctions P)
      (spectralPoint q s) :=
    RationalEvaluation.RegularAt.polynomial P
  have hCreg : RationalEvaluation.RegularAt (RatFunc.C (c : ℂ)) (spectralPoint q s) := by
    simpa using (RationalEvaluation.RegularAt.polynomial (z := spectralPoint q s) (C (c : ℂ)))
  have hXev : RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) RatFunc.X ≠ 0 := by
    rw [RatFunc.eval_X]; exact hz
  have hXreg : RationalEvaluation.RegularAt (RatFunc.X ^ m : RationalFunctions)
      (spectralPoint q s) :=
    RationalEvaluation.RegularAt.zpow hXev m
  have hev := congrArg (RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)) hprod
  rw [RationalEvaluation.eval_subst δ hz (hPdreg.mul hRd'),
    RationalEvaluation.eval_mul hPdreg hRd',
    RationalEvaluation.eval_mul (hCreg.mul hXreg) (hPreg.mul hR),
    RationalEvaluation.eval_mul hCreg hXreg, RationalEvaluation.eval_mul hPreg hR,
    RationalEvaluation.eval_zpow hXev, RatFunc.eval_C, RatFunc.eval_X,
    eval_algebraMap_polynomial, eval_algebraMap_polynomial, RingHom.id_apply, href] at hev
  have hζ : (ζ : ℂ) ^ e ≠ 0 := pow_ne_zero _ ζ.ne_zero
  rw [hev, epsilonMonomial, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  field_simp

end Langlands.RankinSelberg

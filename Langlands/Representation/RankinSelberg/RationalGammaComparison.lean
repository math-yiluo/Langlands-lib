import Langlands.Representation.RankinSelberg.GammaNormalizationAlgebra

/-!
# Constructing a rational gamma comparison from cross identities

This is conditional algebra for already supplied rational families. It does
not establish rational continuation or uniqueness of equivariant forms.
-/

noncomputable section

namespace Langlands.RankinSelberg.RationalGammaComparison

open Polynomial LocalFactor

/-- The candidate obtained from one original and one dual rational value.
In applications `δ = q⁻¹`; `ζ^e` is the prescribed minus-one sign. -/
def gammaRatio (δ ζ : ℂˣ) (e : ℕ) (R Rdual : RationalFunctions) :
    RationalFunctions :=
  RationalReflection.subst δ Rdual / (RatFunc.C ((ζ : ℂ) ^ e) * R)

/-- A reflected rational identity implies the gamma equation on its full
published domain, with precisely its three denominator hypotheses. -/
theorem gammaFunctionalEquation_of_rational_identity {q : ℕ} (hq : 1 < q)
    {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹) {ζ : ℂˣ} {e : ℕ}
    {G R Rdual : RationalFunctions}
    (h : RationalReflection.subst δ Rdual = RatFunc.C ((ζ : ℂ) ^ e) * (G * R)) :
    GammaFunctionalEquation q ζ e G R Rdual := by
  intro s hR hRd hG
  have href : (δ : ℂ) / spectralPoint q s = spectralPoint q (1 - s) := by
    rw [hδ, spectralPoint_one_sub hq]
  have hRd' : RationalEvaluation.RegularAt Rdual ((δ : ℂ) / spectralPoint q s) := by
    rw [href]
    exact hRd
  have hC : RationalEvaluation.RegularAt (RatFunc.C ((ζ : ℂ) ^ e))
      (spectralPoint q s) := by
    simpa using (RationalEvaluation.RegularAt.polynomial
      (z := spectralPoint q s) (C ((ζ : ℂ) ^ e)))
  have hev := congrArg (RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)) h
  rw [RationalEvaluation.eval_subst δ (spectralPoint_ne_zero hq s) hRd', href,
    RationalEvaluation.eval_mul hC
      ((show RationalEvaluation.RegularAt G _ from hG).mul hR),
    RationalEvaluation.eval_mul hG hR, RatFunc.eval_C] at hev
  exact hev

/-- The pointwise and reflected rational formulations are equivalent. -/
theorem gammaFunctionalEquation_iff_rational_identity {q : ℕ} (hq : 1 < q)
    {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹) {ζ : ℂˣ} {e : ℕ}
    {G R Rdual : RationalFunctions} :
    GammaFunctionalEquation q ζ e G R Rdual ↔
      RationalReflection.subst δ Rdual = RatFunc.C ((ζ : ℂ) ^ e) * (G * R) :=
  ⟨GammaNormalization.rational_identity_of_gammaFunctionalEquation hq hδ,
    gammaFunctionalEquation_of_rational_identity hq hδ⟩

/-- Cross multiplication at spectral points outside a finite exceptional set
gives an identity of rational functions. Each of the four original denominators
is required before applying the pointwise hypothesis. -/
theorem rational_cross_of_spectral_cross {q : ℕ} (hq : 1 < q)
    {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (R₀ Rd₀ R Rd : RationalFunctions) (E : Finset ℂ)
    (h : ∀ s : ℂ, spectralPoint q s ∉ E →
      R₀.denom.eval (spectralPoint q s) ≠ 0 →
      Rd₀.denom.eval (spectralPoint q (1 - s)) ≠ 0 →
      R.denom.eval (spectralPoint q s) ≠ 0 →
      Rd.denom.eval (spectralPoint q (1 - s)) ≠ 0 →
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rd *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R₀ =
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rd₀ *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) :
    RationalReflection.subst δ Rd * R₀ = RationalReflection.subst δ Rd₀ * R := by
  let bad : Set ℝ :=
    {t | spectralPoint q (t : ℂ) ∈ E} ∪
    {t | R₀.denom.eval (spectralPoint q t) = 0} ∪
    {t | Rd₀.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0} ∪
    {t | R.denom.eval (spectralPoint q t) = 0} ∪
    {t | Rd.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0}
  have hE : {t : ℝ | spectralPoint q (t : ℂ) ∈ E}.Finite :=
    E.finite_toSet.preimage (spectralPoint_ofReal_injective hq).injOn
  have hbad : bad.Finite :=
    (((hE.union (finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R₀))).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rd₀))).union
      (finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R))).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rd))
  have hU : ((fun t : ℝ => spectralPoint q t) '' badᶜ).Infinite :=
    hbad.infinite_compl.image (spectralPoint_ofReal_injective hq).injOn
  have hpoint : ∀ t ∈ badᶜ,
      RationalEvaluation.RegularAt (RationalReflection.subst δ Rd * R₀)
        (spectralPoint q t) ∧
      RationalEvaluation.RegularAt (RationalReflection.subst δ Rd₀ * R)
        (spectralPoint q t) ∧
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q t)
          (RationalReflection.subst δ Rd * R₀) =
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q t)
          (RationalReflection.subst δ Rd₀ * R) := by
    intro t ht
    simp only [bad, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
    obtain ⟨⟨⟨⟨htE, hR₀⟩, hRd₀⟩, hR⟩, hRd⟩ := ht
    have hz := spectralPoint_ne_zero hq (t : ℂ)
    have href : (δ : ℂ) / spectralPoint q t = spectralPoint q (1 - (t : ℂ)) := by
      rw [hδ, spectralPoint_one_sub hq]
    have hRd₀' : RationalEvaluation.RegularAt Rd₀ ((δ : ℂ) / spectralPoint q t) := by
      rw [href]; exact hRd₀
    have hRd' : RationalEvaluation.RegularAt Rd ((δ : ℂ) / spectralPoint q t) := by
      rw [href]; exact hRd
    refine ⟨(RationalEvaluation.regular_subst δ hz hRd').mul hR₀,
      (RationalEvaluation.regular_subst δ hz hRd₀').mul hR, ?_⟩
    rw [RationalEvaluation.eval_mul (RationalEvaluation.regular_subst δ hz hRd') hR₀,
      RationalEvaluation.eval_mul (RationalEvaluation.regular_subst δ hz hRd₀') hR,
      RationalEvaluation.eval_subst δ hz hRd',
      RationalEvaluation.eval_subst δ hz hRd₀', href]
    exact h t htE hR₀ hRd₀ hR hRd
  apply rationalFunction_eq_of_infinite_eval_eq _ _ _ hU
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).1
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).2.1
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).2.2

/-- One cross identity and a nonzero original anchor identify the comparison
with the explicit quotient. The dual anchor need not be nonzero here. -/
theorem gammaRatio_identity (δ ζ : ℂˣ) (e : ℕ)
    {R₀ Rd₀ R Rd : RationalFunctions} (hR₀ : R₀ ≠ 0)
    (hcross : RationalReflection.subst δ Rd * R₀ =
      RationalReflection.subst δ Rd₀ * R) :
    RationalReflection.subst δ Rd =
      RatFunc.C ((ζ : ℂ) ^ e) * (gammaRatio δ ζ e R₀ Rd₀ * R) := by
  have hC : RatFunc.C ((ζ : ℂ) ^ e) ≠ 0 := by
    exact (_root_.map_ne_zero RatFunc.C).mpr (pow_ne_zero e ζ.ne_zero)
  unfold gammaRatio
  calc
    RationalReflection.subst δ Rd =
        (RationalReflection.subst δ Rd * R₀) / R₀ := by simp [hR₀]
    _ = (RationalReflection.subst δ Rd₀ * R) / R₀ := by rw [hcross]
    _ = RatFunc.C ((ζ : ℂ) ^ e) *
        (RationalReflection.subst δ Rd₀ / (RatFunc.C ((ζ : ℂ) ^ e) * R₀) * R) := by
      field_simp

/-- Nonzero families with pairwise reflected cross identities admit one
nonzero gamma comparison. The two nonzero witnesses may have different
indices; cross multiplication makes the dual anchor nonzero. -/
theorem exists_gammaFunctionalEquation_of_cross {ι : Type*} {q : ℕ}
    (hq : 1 < q) (δ ζ : ℂˣ) (hδ : (δ : ℂ) = (q : ℂ)⁻¹) (e : ℕ)
    (R Rd : ι → RationalFunctions)
    (hR : ∃ i, R i ≠ 0) (hRd : ∃ j, Rd j ≠ 0)
    (hcross : ∀ i j, RationalReflection.subst δ (Rd i) * R j =
      RationalReflection.subst δ (Rd j) * R i) :
    ∃ G : RationalFunctions, G ≠ 0 ∧ ∀ i, GammaFunctionalEquation q ζ e G (R i) (Rd i) := by
  obtain ⟨i₀, hi₀⟩ := hR
  obtain ⟨j₀, hj₀⟩ := hRd
  have hsdj : RationalReflection.subst δ (Rd j₀) ≠ 0 := by
    intro hz
    apply hj₀
    simpa only [RationalReflection.subst_subst, map_zero] using
      congrArg (RationalReflection.subst δ) hz
  have hsdi : RationalReflection.subst δ (Rd i₀) ≠ 0 := by
    intro hz
    have hc := hcross j₀ i₀
    rw [hz, zero_mul] at hc
    exact mul_ne_zero hsdj hi₀ hc
  have hC : RatFunc.C ((ζ : ℂ) ^ e) ≠ 0 :=
    (_root_.map_ne_zero RatFunc.C).mpr (pow_ne_zero e ζ.ne_zero)
  refine ⟨gammaRatio δ ζ e (R i₀) (Rd i₀),
    div_ne_zero hsdi (mul_ne_zero hC hi₀), fun i => ?_⟩
  exact gammaFunctionalEquation_of_rational_identity hq hδ
    (gammaRatio_identity δ ζ e hi₀ (hcross i i₀))

end Langlands.RankinSelberg.RationalGammaComparison

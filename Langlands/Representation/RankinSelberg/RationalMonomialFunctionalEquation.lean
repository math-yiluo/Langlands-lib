import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.RankinSelberg.LaurentTransport
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.Representation.RankinSelberg.RationalEvaluation

/-! # Rational identity of a normalized Laurent monomial functional equation -/

noncomputable section

namespace Langlands.RankinSelberg

open LocalFactor

/-- The nonzero scalar of the spectral reflection `X ↦ q⁻¹/X`. -/
def spectralReflectionUnit {q : ℕ} (hq : 0 < q) : ℂˣ :=
  Units.mk0 ((q : ℂ)⁻¹) (inv_ne_zero (by exact_mod_cast hq.ne'))

@[simp] theorem coe_spectralReflectionUnit {q : ℕ} (hq : 0 < q) :
    (spectralReflectionUnit hq : ℂ) = (q : ℂ)⁻¹ := rfl

/-- A functional equation with both denominator polynomials one is an actual
identity of rational functions after reciprocal spectral substitution. -/
theorem NormalizedFunctionalEquation.rational_identity
    {q : ℕ} (hq : 1 < q) {c : ℂˣ} {m : ℤ} {R RDual : RationalFunctions}
    (hFE : NormalizedFunctionalEquation q 1 1 1 c 0 m R RDual) :
    RationalReflection.subst (spectralReflectionUnit (Nat.zero_lt_one.trans hq)) RDual =
      laurentToRatFunc (laurentMonomialUnit c m : LaurentCoefficients) * R := by
  let δ := spectralReflectionUnit (Nat.zero_lt_one.trans hq)
  have hinj : Function.Injective (fun x : ℂ => (δ : ℂ) / x) := by
    intro x y h
    apply inv_injective
    exact mul_left_cancel₀ δ.ne_zero (by simpa only [div_eq_mul_inv] using h)
  let B : Set ℂ := {x | R.denom.IsRoot x} ∪
    (fun x : ℂ => (δ : ℂ) / x) ⁻¹' {x | RDual.denom.IsRoot x}
  have hB : B.Finite :=
    (Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero R)).union
      ((Polynomial.finite_setOfPred_isRoot (RatFunc.denom_ne_zero RDual)).preimage hinj.injOn)
  let U : Set ℂ :=
    ((fun s : ℝ => spectralPoint q (s : ℂ)) '' Set.Ioi 0) \ B
  have hU : U.Infinite := (infinite_spectralPoints_on_right hq 0).sdiff hB
  have hR (x : ℂ) (hx : x ∈ U) : RationalEvaluation.RegularAt R x := by
    intro hz
    exact hx.2 (Or.inl hz)
  have hD (x : ℂ) (hx : x ∈ U) :
      RationalEvaluation.RegularAt RDual ((δ : ℂ) / x) := by
    intro hz
    exact hx.2 (Or.inr hz)
  have hx0 (x : ℂ) (hx : x ∈ U) : x ≠ 0 := by
    obtain ⟨s, _, rfl⟩ := hx.1
    exact spectralPoint_ne_zero_of_pos (Nat.zero_lt_one.trans hq) _
  have hM (x : ℂ) (hx : x ∈ U) :
      RationalEvaluation.RegularAt
        (laurentToRatFunc (laurentMonomialUnit c m : LaurentCoefficients)) x := by
    exact laurentToRatFunc_regular (Units.mk0 x (hx0 x hx)) _
  apply rationalFunction_eq_of_infinite_eval_eq _ _ U hU
  · intro x hx
    exact RationalEvaluation.regular_subst δ (hx0 x hx) (hD x hx)
  · intro x hx
    exact (hM x hx).mul (hR x hx)
  · intro x hx
    obtain ⟨s, _, hs⟩ := hx.1
    have href : spectralPoint q (1 - (s : ℂ)) = (δ : ℂ) / x := by
      rw [← hs, spectralPoint_sub_one_sub (Nat.zero_lt_one.trans hq)]
      rfl
    have he := hFE (s : ℂ) (by simpa only [hs, RationalEvaluation.RegularAt] using hR x hx)
      (by simpa only [href, RationalEvaluation.RegularAt] using hD x hx)
    rw [RationalEvaluation.eval_subst δ (hx0 x hx) (hD x hx),
      RationalEvaluation.eval_mul (hM x hx) (hR x hx)]
    rw [laurentToRatFunc_monomialUnit]
    have hc : RationalEvaluation.RegularAt (RatFunc.C (c : ℂ)) x := by
      simpa using (RationalEvaluation.RegularAt.polynomial (z := x) (Polynomial.C (c : ℂ)))
    have hX : RatFunc.eval (RingHom.id ℂ) x (RatFunc.X : RationalFunctions) ≠ 0 := by
      simpa using hx0 x hx
    rw [RationalEvaluation.eval_mul hc (RationalEvaluation.RegularAt.zpow hX m),
      RationalEvaluation.eval_zpow hX]
    simpa only [Polynomial.eval_one, Units.val_one, one_pow, one_mul,
      epsilonMonomial, hs, href, RatFunc.eval_C, RatFunc.eval_X, RingHom.id_apply] using he

end Langlands.RankinSelberg

import Langlands.Representation.RankinSelberg.PairLFactor
import Langlands.Representation.RankinSelberg.PairEpsilonFactor
import Langlands.Representation.RankinSelberg.RationalEvaluation

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration
open LocalFactor

universe uF uV uW

/-- The JPSS spectral point obeys the same reflection as the shared arithmetic
spectral parameter. -/
theorem spectralPoint_one_sub {q : ℕ} (hq : 1 < q) (s : ℂ) :
    spectralPoint q (1 - s) = (q : ℂ)⁻¹ / spectralPoint q s := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  rw [spectralPoint_eq_spectralParameter q hq0,
    spectralPoint_eq_spectralParameter q hq0,
    WeilDeligne.spectralParameter_one_sub]
  simp

/-- Rearranging the normalized equation yields epsilon times the L-ratio.
The minus-one central-character sign remains outside that ratio. -/
theorem NormalizedFunctionalEquation.gamma_value
    {q : ℕ} {P Pdual : ℂ[X]} {ζ c : ℂˣ} {e : ℕ} {m : ℤ}
    {R Rdual : RationalFunctions}
    (h : NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual) (s : ℂ)
    (hR : R.denom.eval (spectralPoint q s) ≠ 0)
    (hRd : Rdual.denom.eval (spectralPoint q (1 - s)) ≠ 0)
    (hPd : Pdual.eval (spectralPoint q (1 - s)) ≠ 0) :
    Rdual.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) =
      (ζ : ℂ) ^ e *
        (epsilonMonomial q c m s * P.eval (spectralPoint q s) /
          Pdual.eval (spectralPoint q (1 - s))) *
        R.eval (RingHom.id ℂ) (spectralPoint q s) := by
  apply (mul_left_cancel₀ hPd)
  rw [h s hR hRd]
  field_simp

/-- Evaluation of the rational epsilon monomial at a nonzero input. -/
theorem eval_rationalEpsilonMonomial (c : ℂˣ) (m : ℤ) {z : ℂ} (hz : z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (rationalEpsilonMonomial c m : RationalFunctions) =
      (c : ℂ) * z ^ m := by
  rw [coe_rationalEpsilonMonomial]
  rw [RationalEvaluation.eval_mul
    (by simpa using (RationalEvaluation.RegularAt.polynomial (z := z) (C (c : ℂ))))
    (RationalEvaluation.RegularAt.zpow (R := RatFunc.X) (by simpa using hz) m),
    RationalEvaluation.eval_zpow (R := RatFunc.X) (by simpa using hz)]
  simp

/-- The epsilon monomial has no pole away from zero. -/
theorem regular_rationalEpsilonMonomial (c : ℂˣ) (m : ℤ) {z : ℂ} (hz : z ≠ 0) :
    RationalEvaluation.RegularAt (rationalEpsilonMonomial c m : RationalFunctions) z :=
  RationalEvaluation.RegularAt.of_eval_ne_zero
    (by rw [eval_rationalEpsilonMonomial c m hz]; exact mul_ne_zero c.ne_zero (zpow_ne_zero _ hz))

/-- The explicit rational expression used for gamma; no factor existence is encoded here. -/
def rationalGammaExpression (δ c : ℂˣ) (m : ℤ) (P Pdual : ℂ[X]) : RationalFunctions :=
  (rationalEpsilonMonomial c m : RationalFunctions) *
    algebraMap ℂ[X] RationalFunctions P /
      aeval (RationalReflection.reflectedVariable δ) Pdual

/-- Regularity on the common polynomial domain. Cancellation can make the actual
regular domain larger. -/
theorem regular_rationalGammaExpression (δ c : ℂˣ) (m : ℤ) (P Pdual : ℂ[X])
    {z : ℂ} (hz : z ≠ 0) (hPd : Pdual.eval ((δ : ℂ) / z) ≠ 0) :
    RationalEvaluation.RegularAt (rationalGammaExpression δ c m P Pdual) z := by
  unfold rationalGammaExpression
  rw [div_eq_mul_inv]
  apply ((regular_rationalEpsilonMonomial c m hz).mul
    (RationalEvaluation.RegularAt.polynomial P)).mul
  apply RationalEvaluation.RegularAt.inv
  rwa [RationalEvaluation.eval_aeval (RationalEvaluation.regular_reflectedVariable δ hz),
    RationalEvaluation.eval_reflectedVariable δ hz]

/-- Evaluation of the explicit gamma expression where the displayed denominator is nonzero. -/
theorem eval_rationalGammaExpression (δ c : ℂˣ) (m : ℤ) (P Pdual : ℂ[X])
    {z : ℂ} (hz : z ≠ 0) (hPd : Pdual.eval ((δ : ℂ) / z) ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (rationalGammaExpression δ c m P Pdual) =
      ((c : ℂ) * z ^ m) * P.eval z / Pdual.eval ((δ : ℂ) / z) := by
  unfold rationalGammaExpression
  rw [RationalEvaluation.eval_div
    ((regular_rationalEpsilonMonomial c m hz).mul
      (RationalEvaluation.RegularAt.polynomial P)) (by
      rwa [RationalEvaluation.eval_aeval (RationalEvaluation.regular_reflectedVariable δ hz),
        RationalEvaluation.eval_reflectedVariable δ hz]),
    RationalEvaluation.eval_mul (regular_rationalEpsilonMonomial c m hz)
      (RationalEvaluation.RegularAt.polynomial P), eval_rationalEpsilonMonomial c m hz,
    RatFunc.eval_algebraMap, Polynomial.eval₂_id,
    RationalEvaluation.eval_aeval (RationalEvaluation.regular_reflectedVariable δ hz),
    RationalEvaluation.eval_reflectedVariable δ hz]
  simp

/-- An equality of rational functions, obtained from the normalized equation
at infinitely many real spectral parameters. -/
theorem NormalizedFunctionalEquation.rational_gamma_identity
    {q : ℕ} (hq : 1 < q) {P Pdual : ℂ[X]} {ζ c δ : ℂˣ} {e : ℕ} {m : ℤ}
    {R Rdual : RationalFunctions} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hPd : Pdual ≠ 0)
    (h : NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual) :
    RationalReflection.subst δ Rdual =
      algebraMap ℂ RationalFunctions ((ζ : ℂ) ^ e) *
        (rationalGammaExpression δ c m P Pdual * R) := by
  let G := rationalGammaExpression δ c m P Pdual
  let A := RationalReflection.subst δ Rdual
  let B := algebraMap ℂ RationalFunctions ((ζ : ℂ) ^ e) * (G * R)
  let bad : Set ℝ := {t | R.denom.eval (spectralPoint q t) = 0} ∪
    {t | Rdual.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0} ∪
    {t | Pdual.eval (spectralPoint q (1 - (t : ℂ))) = 0}
  have hbad : bad.Finite :=
    ((finite_spectralPoint_roots hq (RatFunc.denom_ne_zero R)).union
      (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero Rdual))).union
      (finite_reflected_spectralPoint_roots hq hPd)
  have hU : ((fun t : ℝ => spectralPoint q t) '' badᶜ).Infinite :=
    hbad.infinite_compl.image (spectralPoint_ofReal_injective hq).injOn
  have hpoint : ∀ t ∈ badᶜ,
      RationalEvaluation.RegularAt A (spectralPoint q t) ∧
      RationalEvaluation.RegularAt B (spectralPoint q t) ∧
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) A =
        RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) B := by
    intro t ht
    simp only [bad, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or] at ht
    obtain ⟨⟨hR, hRd⟩, hPd'⟩ := ht
    have href : (δ : ℂ) / spectralPoint q t = spectralPoint q (1 - (t : ℂ)) := by
      rw [hδ, spectralPoint_one_sub hq]
    have hz := spectralPoint_ne_zero hq (t : ℂ)
    have hGr : RationalEvaluation.RegularAt G (spectralPoint q t) :=
      regular_rationalGammaExpression δ c m P Pdual hz (by rwa [href])
    have hAr : RationalEvaluation.RegularAt A (spectralPoint q t) :=
      RationalEvaluation.regular_subst δ hz (by simpa [RationalEvaluation.RegularAt, href] using hRd)
    have hsign : RationalEvaluation.RegularAt
        (algebraMap ℂ RationalFunctions ((ζ : ℂ) ^ e)) (spectralPoint q t) := by
      simpa using (RationalEvaluation.RegularAt.polynomial
        (z := spectralPoint q t) (C ((ζ : ℂ) ^ e)))
    refine ⟨hAr, hsign.mul (hGr.mul hR), ?_⟩
    change RatFunc.eval (RingHom.id ℂ) (spectralPoint q t)
      (RationalReflection.subst δ Rdual) = _
    rw [RationalEvaluation.eval_subst δ hz (by
      simpa [RationalEvaluation.RegularAt, href] using hRd), href]
    change _ = RatFunc.eval (RingHom.id ℂ) (spectralPoint q t)
      (algebraMap ℂ RationalFunctions ((ζ : ℂ) ^ e) * (G * R))
    rw [RationalEvaluation.eval_mul hsign (hGr.mul hR),
      RationalEvaluation.eval_mul hGr hR]
    have hev : RatFunc.eval (RingHom.id ℂ) (spectralPoint q t)
        (algebraMap ℂ RationalFunctions ((ζ : ℂ) ^ e)) = (ζ : ℂ) ^ e := by
      change RatFunc.eval (RingHom.id ℂ) (spectralPoint q t) (RatFunc.C ((ζ : ℂ) ^ e)) = _
      exact RatFunc.eval_C _ _
    rw [hev]
    rw [eval_rationalGammaExpression δ c m P Pdual hz (by rwa [href]), href]
    simpa only [epsilonMonomial, mul_assoc] using h.gamma_value t hR hRd hPd'
  apply rationalFunction_eq_of_infinite_eval_eq A B _ hU
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).1
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).2.1
  · rintro x ⟨t, ht, rfl⟩; exact (hpoint t ht).2.2

/-- The gamma equation holds on the full reduced-denominator domain, including
points where the polynomial presentation has canceled zeros. -/
theorem NormalizedFunctionalEquation.gamma_value_of_regular
    {q : ℕ} (hq : 1 < q) {P Pdual : ℂ[X]} {ζ c δ : ℂˣ} {e : ℕ} {m : ℤ}
    {R Rdual : RationalFunctions} (hδ : (δ : ℂ) = (q : ℂ)⁻¹)
    (hPd : Pdual ≠ 0)
    (h : NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual) (s : ℂ)
    (hR : RationalEvaluation.RegularAt R (spectralPoint q s))
    (hRd : RationalEvaluation.RegularAt Rdual (spectralPoint q (1 - s)))
    (hG : RationalEvaluation.RegularAt
      (rationalGammaExpression δ c m P Pdual) (spectralPoint q s)) :
    RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rdual =
      (ζ : ℂ) ^ e * (RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
        (rationalGammaExpression δ c m P Pdual) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) := by
  have href : (δ : ℂ) / spectralPoint q s = spectralPoint q (1 - s) := by
    rw [hδ, spectralPoint_one_sub hq]
  rw [← href, ← RationalEvaluation.eval_subst δ (spectralPoint_ne_zero hq s)
    (by simpa [href] using hRd), h.rational_gamma_identity hq hδ hPd,
    RationalEvaluation.eval_mul (by simpa using
      (RationalEvaluation.RegularAt.polynomial (z := spectralPoint q s) (C ((ζ : ℂ) ^ e))))
      (hG.mul hR), RationalEvaluation.eval_mul hG hR]
  have hev : RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
      (algebraMap ℂ RationalFunctions ((ζ : ℂ) ^ e)) = (ζ : ℂ) ^ e := by
    change RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) (RatFunc.C ((ζ : ℂ) ^ e)) = _
    exact RatFunc.eval_C _ _
  rw [hev]

section Pair

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F} {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}

variable [BorelSpace F] [T2Space F] [TotallyDisconnectedSpace F]

variable [Measure.IsMulRightInvariant (unipotentHaar F n)]

/-- The gamma factor `ε(s) L(1-s, π^ι × σ^ι) / L(s, π × σ)` as a unit rational
function. Each L-factor and the epsilon factor need their own existence proof.
The inverse-transpose pullbacks have not been identified with contragredients. -/
def pairGammaFactor (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (_hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ)
    (hL : PairLPolynomialExists q ψ abv μ ν π σ)
    (hdual : DualPairLPolynomialExists q ψ abv μ ν π σ) : RationalFunctionsˣ :=
  pairEpsilonFactor hν hε *
    Units.map (RationalReflection.subst
      (WeilDeligne.reflectionScale (q : ℝ)
        (by exact_mod_cast (show 0 < q by omega)))).toMonoidHom (dualPairLFactor hdual) /
    pairLFactor hL

/-- The defining ratio, using the already published rational reflection. -/
theorem coe_pairGammaFactor (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ)
    (hL : PairLPolynomialExists q ψ abv μ ν π σ)
    (hdual : DualPairLPolynomialExists q ψ abv μ ν π σ) :
    (pairGammaFactor hq hν hμ hε hL hdual : RationalFunctions) =
      (pairEpsilonFactor hν hε : RationalFunctions) *
        RationalReflection.subst
          (WeilDeligne.reflectionScale (q : ℝ)
            (by exact_mod_cast (show 0 < q by omega)))
          (dualPairLFactor hdual : RationalFunctions) /
        (pairLFactor hL : RationalFunctions) := by
  simp [pairGammaFactor]

/-- The exact polynomial formula for the constructed gamma factor. -/
theorem pairGammaFactor_eq (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ)
    (hL : PairLPolynomialExists q ψ abv μ ν π σ)
    (hdual : DualPairLPolynomialExists q ψ abv μ ν π σ)
    {e : ℂˣ × ℤ} {P Pdual : ℂ[X]}
    (he : IsPairEpsilonFactor q ψ abv ν π σ e)
    (hP : IsPairLPolynomial q ψ abv μ ν π σ P)
    (hPd : IsDualPairLPolynomial q ψ abv μ ν π σ Pdual) :
    (pairGammaFactor hq hν hμ hε hL hdual : RationalFunctions) =
      (rationalEpsilonMonomial e.1 e.2 : RationalFunctions) *
        algebraMap ℂ[X] RationalFunctions P /
        aeval (RationalReflection.reflectedVariable
          (WeilDeligne.reflectionScale (q : ℝ)
            (by exact_mod_cast (show 0 < q by omega)))) Pdual := by
  rw [coe_pairGammaFactor, pairEpsilonFactor_eq hq hν hε he,
    dualPairLFactor_eq hdual hPd, pairLFactor_eq hL hP, map_inv₀,
    RationalReflection.subst_polynomial, div_inv_eq_mul]
  ring

omit [Measure.IsMulRightInvariant (unipotentHaar F n)] in
/-- The complex epsilon value agrees with rational evaluation at every spectral point. -/
theorem eval_pairEpsilonFactor (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ) (s : ℂ) :
    RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
      (pairEpsilonFactor hν hε : RationalFunctions) = (pairEpsilonValue hq hν hε s : ℂ) :=
  eval_rationalEpsilonMonomial _ _ (spectralPoint_ne_zero hq s)

/-- The pair gamma constructor is the explicit rational expression of any witnesses. -/
theorem pairGammaFactor_eq_expression (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ)
    (hL : PairLPolynomialExists q ψ abv μ ν π σ)
    (hdual : DualPairLPolynomialExists q ψ abv μ ν π σ)
    {e : ℂˣ × ℤ} {P Pdual : ℂ[X]}
    (he : IsPairEpsilonFactor q ψ abv ν π σ e)
    (hP : IsPairLPolynomial q ψ abv μ ν π σ P)
    (hPd : IsDualPairLPolynomial q ψ abv μ ν π σ Pdual) :
    (pairGammaFactor hq hν hμ hε hL hdual : RationalFunctions) =
      rationalGammaExpression (WeilDeligne.reflectionScale (q : ℝ)
        (by exact_mod_cast (show 0 < q by omega))) e.1 e.2 P Pdual :=
  pairGammaFactor_eq hq hν hμ hε hL hdual he hP hPd

/-- Gamma satisfies the unnormalized equation for any normalized equation using
these intrinsic L-polynomials and the pair epsilon witness. Only the reduced
denominators of the continuations and gamma are excluded. -/
theorem pairGammaFactor_functional_equation (hq : 1 < q) (hν : IsSelfDual ψ ν)
    (hμ : IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
      (unipotentHaar F n) μ)
    (hε : PairEpsilonFactorExists q ψ abv ν π σ)
    (hL : PairLPolynomialExists q ψ abv μ ν π σ)
    (hdual : DualPairLPolynomialExists q ψ abv μ ν π σ)
    {e : ℂˣ × ℤ} {P Pdual : ℂ[X]} {ζ : ℂˣ} {d : ℕ} {R Rdual : RationalFunctions}
    (he : IsPairEpsilonFactor q ψ abv ν π σ e)
    (hP : IsPairLPolynomial q ψ abv μ ν π σ P)
    (hPd : IsDualPairLPolynomial q ψ abv μ ν π σ Pdual)
    (h : NormalizedFunctionalEquation q P Pdual ζ e.1 d e.2 R Rdual) (s : ℂ)
    (hR : R.denom.eval (spectralPoint q s) ≠ 0)
    (hRd : Rdual.denom.eval (spectralPoint q (1 - s)) ≠ 0)
    (hG : (pairGammaFactor hq hν hμ hε hL hdual : RationalFunctions).denom.eval
      (spectralPoint q s) ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) Rdual =
      (ζ : ℂ) ^ d * (RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
        (pairGammaFactor hq hν hμ hε hL hdual : RationalFunctions) *
          RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) := by
  rw [pairGammaFactor_eq_expression hq hν hμ hε hL hdual he hP hPd] at hG ⊢
  exact h.gamma_value_of_regular hq (by simp) hPd.ne_zero s hR hRd hG

end Pair

end Langlands.RankinSelberg

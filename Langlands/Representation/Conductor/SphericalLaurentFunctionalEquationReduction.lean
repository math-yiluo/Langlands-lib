import Langlands.Representation.Conductor.SphericalLaurentFunctionalEquationStatement
import Langlands.Representation.Conductor.SphericalCorankOneFunctionalEquationStatement
import Langlands.Representation.Conductor.SphericalLFactorGenerationStatement
import Langlands.Representation.Conductor.SphericalUnitaryExtension
import Langlands.Representation.Conductor.SphericalDualParameters
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Reduction of the all-parameter spherical functional equation

The corank-one spherical functional equation for unitary Satake parameters
(`SphericalCorankOneFunctionalEquationStatement`) and the L-factor facts of JPSS 1983 for
spherical test vectors (`SphericalLFactorGenerationStatement`: the standard L-polynomial,
convergence, and the Laurent numerator for every Satake parameter) imply the functional
equation with Laurent numerator for every Satake parameter
(`SphericalLaurentFunctionalEquationStatement`).
-/

noncomputable section

namespace Langlands.Conductor

open Polynomial Filter Topology MeasureTheory
open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg

universe uF uV

/-! ### Rational continuations from Laurent numerators -/

/-- A polynomial that does not vanish at `0` does not vanish at `q^(-s)` on a right
half-plane. -/
theorem exists_halfPlane_eval_spectralPoint_ne_zero {q : ℕ} (hq : 1 < q) (D : ℂ[X])
    (hD : D.eval 0 ≠ 0) : ∃ b : ℝ, ∀ s : ℂ, b < s.re → D.eval (spectralPoint q s) ≠ 0 := by
  have hev : ∀ᶠ z in 𝓝 (0 : ℂ), D.eval z ≠ 0 :=
    D.continuous.continuousAt.eventually_ne hD
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨-Real.logb q δ, fun s hs => hball ?_⟩
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hnorm : ‖spectralPoint q s‖ = (q : ℝ) ^ (-s.re) := by
    unfold spectralPoint
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  rw [dist_zero_right, hnorm]
  calc (q : ℝ) ^ (-s.re) < (q : ℝ) ^ (Real.logb q δ) :=
        Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)
    _ = δ := Real.rpow_logb (by linarith) hq1.ne' hδ

/-- If `f(s) ∏ P(x_i q^(-s)) = q^(-Ns) Q(q^(-s))` on a right half-plane and `P(0) = 1`, then
`f` has the rational continuation `X^N Q · ∏ P(x_i X)⁻¹`. -/
theorem hasRationalContinuation_laurent_mul_essentialFactor {q : ℕ} (hq : 1 < q) {m : ℕ}
    {P : ℂ[X]} (hP : P.coeff 0 = 1) (x : Fin m → ℂˣ) {f : ℂ → ℂ} {a : ℝ} {N : ℤ} {Q : ℂ[X]}
    (hf : ∀ s : ℂ, a < s.re →
      f s * (∏ i, P.comp (C (x i : ℂ) * X)).eval (spectralPoint q s) =
        spectralPoint q s ^ N * Q.eval (spectralPoint q s)) :
    HasRationalContinuation q f
      (laurentToRatFunc (LaurentPolynomial.T N * Q.toLaurent) * essentialFactor P x) := by
  set D : ℂ[X] := ∏ i, P.comp (C (x i : ℂ) * X) with hDdef
  have hD0 : D.eval 0 ≠ 0 := by
    rw [hDdef, Polynomial.eval_prod]
    rw [Finset.prod_eq_one fun i _ => by
      rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        mul_zero, ← Polynomial.coeff_zero_eq_eval_zero, hP]]
    exact one_ne_zero
  obtain ⟨b, hb⟩ := exists_halfPlane_eval_spectralPoint_ne_zero hq D hD0
  refine ⟨max a b, fun s hs => ?_⟩
  have hsa : a < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsb : b < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hz : spectralPoint q s ≠ 0 := spectralPoint_ne_zero hq s
  have hDz : D.eval (spectralPoint q s) ≠ 0 := hb s hsb
  have hev : RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
      (algebraMap ℂ[X] RationalFunctions D) = D.eval (spectralPoint q s) := by
    rw [RatFunc.eval_algebraMap]
    simp
  have hreg1 : RationalEvaluation.RegularAt
      (laurentToRatFunc (LaurentPolynomial.T N * Q.toLaurent)) (spectralPoint q s) :=
    laurentToRatFunc_regular (Units.mk0 _ hz) _
  have hreg2 : RationalEvaluation.RegularAt (essentialFactor P x) (spectralPoint q s) := by
    rw [essentialFactor_eq]
    exact RationalEvaluation.RegularAt.inv (by rw [hev]; exact hDz)
  refine ⟨hreg1.mul hreg2, ?_⟩
  rw [RationalEvaluation.eval_mul hreg1 hreg2, essentialFactor_eq,
    RationalEvaluation.eval_inv (by rw [hev]; exact hDz), hev]
  have hL : RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
      (laurentToRatFunc (LaurentPolynomial.T N * Q.toLaurent)) =
        spectralPoint q s ^ N * Q.eval (spectralPoint q s) := by
    have := eval_laurentToRatFunc (Units.mk0 _ hz) (LaurentPolynomial.T N * Q.toLaurent)
    rw [Units.val_mk0] at this
    rw [this, map_mul (laurentEval _), laurentEval_T, laurentEval_toLaurent, Units.val_mk0]
  rw [hL, ← hf s hsa, mul_inv_cancel_right₀ hDz]

/-! ### The reduction -/

/-- **Reduction.** The corank-one spherical functional equation for unitary Satake
parameters, together with the spherical L-factor facts of JPSS 1983 (existence of the
standard L-polynomial, convergence, and the Laurent numerator for every Satake parameter),
implies the corank-one spherical functional equation with Laurent numerator for every
Satake parameter. -/
theorem sphericalLaurentFunctionalEquation_of_corankOne_of_generation
    (hFE : SphericalCorankOneFunctionalEquationStatement.{uF, uV})
    (hgen : SphericalLFactorGenerationStatement.{uF, uV}) :
    SphericalLaurentFunctionalEquationStatement.{uF, uV} := by
  intro F _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ q ψ abv ϖ μ h ν hν V _ _ π hπ ℓ hℓ P hP c m hε
  have hq : 1 < q := h.one_lt_q
  have h' : IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ := h.scaleNegOne
  have hP1 : P.coeff 0 = 1 := hP.1
  -- the contragredient side
  set πd := inverseTransposePullback π with hπd
  set ℓd := scaledDualFunctional ψ π ℓ with hℓd
  have hπd : IsGeneric (ψ.scale (-1)) (n + 1) πd := isGeneric_inverseTransposePullback ψ π hπ
  have hℓd0 : ℓd.val ≠ 0 := scaledDualFunctional_ne_zero ψ π ℓ hℓ
  -- the L-factor facts for `π` and for its inverse-transpose pullback
  obtain ⟨P₀, hP₀, hconvF, hlaurF, -⟩ := hgen F n q ψ abv ϖ μ h π hπ ℓ hℓ
  rw [IsNormalizedGenerator.unique hP₀ hP] at hlaurF
  obtain ⟨Pdual, hPdual, hconvD, hlaurD, -⟩ := hgen F n q (ψ.scale (-1)) abv ϖ μ h' πd hπd ℓd hℓd0
  have hPd1 : Pdual.coeff 0 = 1 := hPdual.1
  refine ⟨Pdual, hPd1, fun v x => ?_⟩
  obtain ⟨u, hu⟩ := v.property
  -- the dual pair as a coefficient of the inverse-transpose pullback
  set vd : (coefficientModel πd ℓd).toSubmodule := ⟨coefficientMap πd ℓd u, ⟨u, rfl⟩⟩ with hvd
  have hdualF : firstDualFunction ψ (n + 1) v.val = vd.val := by
    rw [← hu]
    exact firstDualFunction_coefficient ψ π ℓ u
  have hdualW : ∀ y : Fin (n + 1) → ℂˣ,
      secondDualFunction ψ n (inverseSphericalWhittaker h.conductor.1 h.uniformizer q y) =
        inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q y⁻¹ :=
    fun y => secondDualFunction_inverseSphericalWhittaker h.conductor.1 h.uniformizer q
      h'.conductor.1 y
  -- Laurent numerators for every parameter
  have hQ : ∀ y : Fin (n + 1) → ℂˣ, ∃ Q : LaurentPolynomial ℂ,
      HasRationalContinuation q
        (corankOneIntegral ψ abv μ v.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q y))
        (laurentToRatFunc Q * essentialFactor P y) := by
    intro y
    obtain ⟨a, N, Q, hN⟩ := hlaurF v y
    exact ⟨_, hasRationalContinuation_laurent_mul_essentialFactor hq hP1 y hN⟩
  have hQd : ∀ y : Fin (n + 1) → ℂˣ, ∃ Q : LaurentPolynomial ℂ,
      HasRationalContinuation q
        (corankOneIntegral (ψ.scale (-1)) abv μ vd.val
          (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q y⁻¹))
        (laurentToRatFunc Q * essentialFactor Pdual y⁻¹) := by
    intro y
    obtain ⟨a, N, Q, hN⟩ := hlaurD vd y⁻¹
    exact ⟨_, hasRationalContinuation_laurent_mul_essentialFactor hq hPd1 y⁻¹ hN⟩
  choose Qf hQf using hQ
  choose Qdf hQdf using hQd
  -- the functional equation for unitary parameters, from the unitary statement
  have hunit : ∀ y : Fin (n + 1) → ℂˣ, (∀ i, ‖(y i : ℂ)‖ = 1) →
      NormalizedFunctionalEquation q (∏ i, P.comp (C (y i : ℂ) * X))
        (∏ i, Pdual.comp (C (((y i)⁻¹ : ℂˣ) : ℂ) * X)) 1 (c ^ (n + 1) * (∏ i, y i) ^ m)
        (n + 1) (((n + 1 : ℕ) : ℤ) * m)
        (laurentToRatFunc (Qf y) * essentialFactor P y)
        (laurentToRatFunc (Qdf y) * essentialFactor Pdual y⁻¹) := by
    intro y hy
    obtain ⟨-, -, R, Rdual, hR, hRd, hNFE⟩ :=
      hFE F n q ψ abv ϖ μ h h' ν hν π hπ ℓ hℓ ℓd (scaledDualFunctional_val ψ π ℓ) c m hε
        P Pdual hP hPdual u y hy
    have hR' : R = laurentToRatFunc (Qf y) * essentialFactor P y := by
      apply HasRationalContinuation.unique hq hR
      have hu' : coefficientMap π ℓ u = v.val := hu
      rw [hu']
      exact hQf y
    have hRd' : Rdual = laurentToRatFunc (Qdf y) * essentialFactor Pdual y⁻¹ :=
      HasRationalContinuation.unique hq hRd (hQdf y)
    subst hR' hRd'
    intro s hs hsd
    have := hNFE s hs hsd
    simpa only [Units.val_one, one_pow, Pi.inv_apply] using this
  -- convergence for every parameter
  have hconvd : ∀ y : Fin (n + 1) → ℂˣ, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges (ψ.scale (-1)) abv μ vd.val
        (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q y⁻¹) s :=
    fun y => hconvD vd y⁻¹
  have hFEx := normalizedFunctionalEquation_of_unitary h h' π hπ.2.1.1 ℓ πd hπd.2.1.1 ℓd v vd
    hP1 hPd1 1 (c ^ (n + 1)) (n + 1) m (((n + 1 : ℕ) : ℤ) * m) (fun y => hconvF v y) hconvd
    Qf Qdf hQf hQdf hunit x
  refine ⟨hconvF v x, ?_, Qf x, laurentToRatFunc (Qdf x) * essentialFactor Pdual x⁻¹,
    hQf x, ?_, hFEx⟩
  · rw [hdualF, hdualW]
    exact hconvd x
  · rw [hdualF, hdualW]
    exact hQdf x

end Langlands.Conductor

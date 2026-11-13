import Langlands.Representation.Conductor.EssentialExistenceReduction
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentReflection
import Langlands.Representation.RankinSelberg.BilateralSpectralEvaluation

/-!
# The spherical corank-one functional equation: from unitary to all Satake parameters

Let `π` be a smooth representation of `GL_(n+2)(F)` with a Whittaker functional, and `w` a
model vector. For a tuple `x` of Satake parameters, suppose that the corank-one integral
`Ψ(s, w, W(·; x; ψ̄))` converges on a right half-plane and continues to
`Q_x(X) ∏ P(x_i X)⁻¹`, with `Q_x` a Laurent polynomial in `X = q^(-s)`. The coefficients of
`Q_x` are then the values at `x` of fixed Laurent polynomials in the torus coordinates
(the coefficients of Jacquet's formal series `Ψ(X; W) ∏ P(X X_i)`). The same holds for the
dual integral. Hence the normalized functional equation, which is an identity of Laurent
polynomials in `X`, has coefficients that are Laurent polynomials in `x`. A Laurent polynomial
on the torus that vanishes on the compact torus `|x_i| = 1` is zero, so the equation for all
unitary `x` gives it for all `x`.
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Polynomial Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.BilateralSpectralEvaluation
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

/-! ### The unit circle and the compact torus -/

/-- The unit circle in `ℂ` is infinite. -/
theorem setOf_norm_eq_one_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  let f : Set.Ioo (0 : ℝ) 1 → ℂ := fun t => ⟨t, Real.sqrt (1 - (t : ℝ) ^ 2)⟩
  have hf : Function.Injective f := by
    intro s t hst
    exact Subtype.ext (congrArg Complex.re hst)
  have : Infinite (Set.Ioo (0 : ℝ) 1) :=
    (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).to_subtype
  refine Set.infinite_of_injective_forall_mem hf (fun t => ?_)
  have h0 := t.2.1
  have h1 := t.2.2
  have ht1 : 0 ≤ 1 - (t : ℝ) ^ 2 := by nlinarith
  have hsq : ‖f t‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_mk, Real.mul_self_sqrt ht1]
    ring
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq

section Torus

variable (σ : Type*) [Fintype σ] (K : Type*) [Field K]

/-- Each torus coordinate is a unit of the Laurent coordinate ring. -/
theorem isUnit_torusCoordinate (i : σ) :
    IsUnit (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (MvPolynomial.X i)) :=
  isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    (IsLocalization.Away.algebraMap_isUnit (S := TorusPolynomialAlgebra σ K)
      (∏ j : σ, (MvPolynomial.X j : MvPolynomial σ K)))

/-- The inverse `X_i⁻¹` of a torus coordinate. -/
def torusInverseCoordinate (i : σ) : TorusPolynomialAlgebra σ K :=
  (((isUnit_torusCoordinate σ K i).unit)⁻¹ : (TorusPolynomialAlgebra σ K)ˣ)

/-- The inversion `X_i ↦ X_i⁻¹` of the Laurent coordinate ring. -/
def torusPolynomialInversion :
    TorusPolynomialAlgebra σ K →ₐ[K] TorusPolynomialAlgebra σ K :=
  IsLocalization.Away.liftAlgHom (∏ i : σ, (MvPolynomial.X i : MvPolynomial σ K))
    (f := MvPolynomial.aeval (torusInverseCoordinate σ K)) (by
      rw [map_prod]
      simp only [MvPolynomial.aeval_X, torusInverseCoordinate]
      rw [← Units.coe_prod]
      exact Units.isUnit _)

theorem torusPolynomialInversion_algebraMap (p : MvPolynomial σ K) :
    torusPolynomialInversion σ K
        (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) p) =
      MvPolynomial.aeval (torusInverseCoordinate σ K) p := by
  simp [torusPolynomialInversion, IsLocalization.Away.liftAlgHom]

theorem torusPolynomialEvaluation_inverseCoordinate (x : σ → Kˣ) (i : σ) :
    torusPolynomialEvaluation σ K x (torusInverseCoordinate σ K i) = (x i : K)⁻¹ := by
  rw [torusInverseCoordinate, map_units_inv, IsUnit.unit_spec,
    torusPolynomialEvaluation_algebraMap, MvPolynomial.aeval_X]

/-- Evaluating the inversion at `x` is evaluation at `x⁻¹`. -/
theorem torusPolynomialEvaluation_inversion (x : σ → Kˣ) (p : TorusPolynomialAlgebra σ K) :
    torusPolynomialEvaluation σ K x (torusPolynomialInversion σ K p) =
      torusPolynomialEvaluation σ K x⁻¹ p := by
  have hext : (torusPolynomialEvaluation σ K x).comp (torusPolynomialInversion σ K) =
      torusPolynomialEvaluation σ K x⁻¹ := by
    apply IsLocalization.algHom_ext
      (Submonoid.powers (∏ i : σ, (MvPolynomial.X i : MvPolynomial σ K)))
    apply MvPolynomial.algHom_ext
    intro i
    change torusPolynomialEvaluation σ K x (torusPolynomialInversion σ K
        (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (MvPolynomial.X i))) =
      torusPolynomialEvaluation σ K x⁻¹
        (algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (MvPolynomial.X i))
    rw [torusPolynomialInversion_algebraMap, MvPolynomial.aeval_X,
      torusPolynomialEvaluation_inverseCoordinate, torusPolynomialEvaluation_algebraMap,
      MvPolynomial.aeval_X, Pi.inv_apply, Units.val_inv_eq_inv_val]
  exact DFunLike.congr_fun hext p

variable {σ}

/-- A complex Laurent polynomial on the torus that vanishes on the compact torus
`|x_i| = 1` is zero. -/
theorem torusPolynomial_eq_zero_of_unitary_evaluations (p : TorusPolynomialAlgebra σ ℂ)
    (hp : ∀ x : σ → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) → torusPolynomialEvaluation σ ℂ x p = 0) :
    p = 0 := by
  obtain ⟨m, a, ha⟩ :=
    IsLocalization.Away.surj (∏ i : σ, (MvPolynomial.X i : MvPolynomial σ ℂ)) p
  have hazero : a = 0 := by
    apply MvPolynomial.funext_set (fun _ : σ => {z : ℂ | ‖z‖ = 1})
      (fun _ => setOf_norm_eq_one_infinite)
    intro x hx
    have hx1 : ∀ i, ‖x i‖ = 1 := fun i => hx i (Set.mem_univ i)
    have hx0 : ∀ i, x i ≠ 0 := fun i h0 => by
      have := hx1 i
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    let xu : σ → ℂˣ := fun i => Units.mk0 (x i) (hx0 i)
    have he := congrArg (torusPolynomialEvaluation σ ℂ xu) ha
    rw [map_mul, hp xu hx1, zero_mul, torusPolynomialEvaluation_algebraMap] at he
    change (0 : ℂ) = MvPolynomial.eval x a at he
    simpa only [map_zero] using he.symm
  rw [hazero, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit
    (S := TorusPolynomialAlgebra σ ℂ) (∏ i : σ, (MvPolynomial.X i : MvPolynomial σ ℂ))).pow m
      ).mul_left_eq_zero.mp ha

end Torus

/-! ### Laurent identities equivalent to the normalized functional equation -/

/-- With `R = Q · ∏ P(x_i X)⁻¹`, the Laurent polynomial `Q` is `∏ P(x_i X)` times `R`. -/
theorem laurentToRatFunc_eq_algebraMap_prod_mul_essentialFactor {m : ℕ} {P : ℂ[X]}
    (hP : P.coeff 0 = 1) (x : Fin m → ℂˣ) (Q : LaurentPolynomial ℂ) :
    laurentToRatFunc Q =
      algebraMap ℂ[X] RationalFunctions (∏ i, P.comp (C (x i : ℂ) * X)) *
        (laurentToRatFunc Q * essentialFactor P x) := by
  have hD : (∏ i, P.comp (C (x i : ℂ) * X)) ≠ 0 := by
    intro h0
    have h1 : (∏ i, P.comp (C (x i : ℂ) * X)).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
      apply Finset.prod_eq_one
      intro i _
      rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        mul_zero, ← Polynomial.coeff_zero_eq_eval_zero, hP]
    rw [h0, Polynomial.coeff_zero] at h1
    exact zero_ne_one h1
  rw [essentialFactor_eq, mul_comm (laurentToRatFunc Q), ← mul_assoc,
    mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hD), one_mul]

/-- A Laurent identity `Ld(q⁻¹X⁻¹) = ζ^e c X^d L(X)` between the numerators gives the
normalized functional equation of the rational functions `R`, `Rd` they clear. -/
theorem normalizedFunctionalEquation_of_laurent_identity {q : ℕ} (hq : 0 < q)
    {P Pdual : ℂ[X]} {ζ c : ℂˣ} {e : ℕ} {d : ℤ}
    {R Rd : RationalFunctions} {L Ld : LaurentPolynomial ℂ}
    (hL : laurentToRatFunc L = algebraMap ℂ[X] RationalFunctions P * R)
    (hLd : laurentToRatFunc Ld = algebraMap ℂ[X] RationalFunctions Pdual * Rd)
    (hid : reflectLaurent q hq Ld =
      (LaurentPolynomial.C ((ζ : ℂ) ^ e * (c : ℂ)) * LaurentPolynomial.T d) * L) :
    NormalizedFunctionalEquation q P Pdual ζ c e d R Rd := by
  intro s hR hRd
  have h1 := laurentEval_eq_of_laurentToRatFunc_eq (spectralUnit hq (1 - s)) hLd hRd
  have h2 := laurentEval_eq_of_laurentToRatFunc_eq (spectralUnit hq s) hL hR
  have h3 := congrArg (laurentEval (spectralUnit hq s)) hid
  rw [laurentEval_reflectLaurent, map_mul, map_mul, laurentEval_C, laurentEval_T, h1, h2] at h3
  simpa only [coe_spectralUnit, epsilonMonomial, mul_assoc] using h3

/-- The coefficients of the reflection `L(q⁻¹X⁻¹)`. -/
theorem reflectLaurent_coeff {q : ℕ} (hq : 0 < q) (L : LaurentPolynomial ℂ) (j : ℤ) :
    (reflectLaurent q hq L).coeff j = (q : ℂ) ^ j * L.coeff (-j) := by
  have h := congrArg (fun a : BilateralLaurentSeries => a j)
    (reflectSeries_ofLaurentPolynomial q hq L)
  simpa only [reflectSeries_apply, ofLaurentPolynomial_apply] using h.symm

/-- The coefficients of `a X^k L(X)`. -/
theorem monomial_mul_laurent_coeff (a : ℂ) (k : ℤ) (L : LaurentPolynomial ℂ) (j : ℤ) :
    (LaurentPolynomial.C a * LaurentPolynomial.T k * L).coeff j = a * L.coeff (j - k) := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single_mul_apply,
    neg_add_eq_sub]

/-! ### Coefficients of the Laurent numerator -/

section Model

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)

/-- **Coefficients of the numerator.** If the corank-one integral of `w` against
`W(·; x; ψ̄)` converges on a right half-plane and continues to `Q ∏ P(x_i X)⁻¹`, then the
`d`-th coefficient of the Laurent polynomial `Q` is the value at `x` of the `d`-th
coefficient of Jacquet's formal series `Ψ(X; W) ∏ P(X X_i)`, a symmetric Laurent
polynomial in the torus coordinates that does not depend on `x`. -/
theorem laurentNumerator_coeff_eq_specialized {P : ℂ[X]} (hP : P.coeff 0 = 1)
    (w : (coefficientModel π ℓ).toSubmodule) (x : Fin (n + 1) → ℂˣ)
    (hconv : ∃ a : ℝ, ∀ s : ℂ, a < s.re → CorankOneConverges ψ abv μ w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)
    {Q : LaurentPolynomial ℂ}
    (hQ : HasRationalContinuation q (corankOneIntegral ψ abv μ w.val
      (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x))
      (laurentToRatFunc Q * essentialFactor P x)) (d : ℤ) :
    Q.coeff d = symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      ((corankOneModelDenominatorProduct h π hπ ℓ w P).coeff d) := by
  have hq : 1 < q := h.one_lt_q
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  obtain ⟨a₁, ha₁⟩ := hconv
  obtain ⟨a₂, ha₂⟩ := hQ
  obtain ⟨d₀, hd₀⟩ := corankOneModelDenominatorProduct_coeff_eq_zero_below h π hπ ℓ w
  obtain ⟨d₁, hd₁⟩ : ∃ d₁ : ℤ, ∀ e < d₁, Q.coeff e = 0 := by
    obtain ⟨b, hb⟩ := Q.coeff.support.bddBelow
    refine ⟨b, fun e he => ?_⟩
    by_contra hne
    exact absurd (hb (Finsupp.mem_support_iff.mpr hne)) (not_le.mpr he)
  have hL := laurentToRatFunc_eq_algebraMap_prod_mul_essentialFactor hP x Q
  have hzero := eq_zero_of_hasSum_int_eq_zero
    (c := fun e => symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      ((corankOneModelDenominatorProduct h π hπ ℓ w P).coeff e) - Q.coeff e)
    (d₀ := min d₀ d₁)
    (fun e he => by
      rw [hd₀ P e (lt_of_lt_of_le he (min_le_left _ _)),
        hd₁ e (lt_of_lt_of_le he (min_le_right _ _)), map_zero, sub_zero])
    (Real.rpow_pos_of_pos hqr (-(max a₁ a₂)))
    (fun y hy hyr => by
      obtain ⟨s, hs, hsy⟩ := exists_spectralPoint_eq hq (max a₁ a₂) hy hyr
      have hs1 : a₁ < (s : ℂ).re := by
        rw [Complex.ofReal_re]
        exact lt_of_le_of_lt (le_max_left _ _) hs
      have hs2 : a₂ < (s : ℂ).re := by
        rw [Complex.ofReal_re]
        exact lt_of_le_of_lt (le_max_right _ _) hs
      have h1 := hasSum_specializedDenominatorProduct h π hπ ℓ P w x s (ha₁ s hs1)
      obtain ⟨hden, hval⟩ := ha₂ s hs2
      have h2 := hasSum_ofLaurentPolynomial (spectralUnit hq0 (s : ℂ)) Q
      have h3 := laurentEval_eq_of_laurentToRatFunc_eq (spectralUnit hq0 (s : ℂ)) hL hden
      rw [h3, coe_spectralUnit, ← hval] at h2
      have h4 := h1.sub h2
      rw [sub_self, hsy] at h4
      convert h4 using 1
      funext e
      rw [sub_mul]
      rfl)
    d
  exact (sub_eq_zero.mp hzero).symm

end Model

/-! ### From unitary parameters to all parameters -/

section Extension

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}

/-- **Unitary to all parameters.** Let `π` (with `ψ`-functional `ℓ`, model vector `w`, and
polynomial `P`) and `ρ` (with `ψ̄`-functional `ℓ'`, model vector `w'`, and polynomial `Pd`) be
smooth representations of `GL_(n+2)(F)`, under Jacquet's normalizations `h` for `ψ` and `h'`
for `ψ̄`. Suppose that for every tuple `x` of Satake parameters the integrals
`Ψ(s, w, W(·; x; ψ̄))` and `Ψ(s, w', W(·; x⁻¹; ψ))` converge on right half-planes and
continue to `Q x · ∏ P(x_i X)⁻¹` and `Qd x · ∏ Pd(x_i⁻¹ X)⁻¹` with Laurent polynomials
`Q x`, `Qd x`. If the normalized functional equation with epsilon factor
`c (∏ x_i)^m q^(-ks)` and sign `ζ^e` holds for every `x` with `|x_i| = 1`, it holds for every
`x`. -/
theorem normalizedFunctionalEquation_of_unitary
    (h : IsJacquetNormalization q ψ abv ϖ μ)
    (h' : IsJacquetNormalization q (ψ.scale (-1)) abv ϖ μ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V) (hπ : IsSmooth π)
    (ℓ : glFunctionals ψ (n + 1) π)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) W) (hρ : IsSmooth ρ)
    (ℓ' : glFunctionals (ψ.scale (-1)) (n + 1) ρ)
    (w : (coefficientModel π ℓ).toSubmodule) (w' : (coefficientModel ρ ℓ').toSubmodule)
    {P Pd : ℂ[X]} (hP : P.coeff 0 = 1) (hPd : Pd.coeff 0 = 1)
    (ζ c : ℂˣ) (e : ℕ) (m k : ℤ)
    (hconv : ∀ x : Fin (n + 1) → ℂˣ, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv μ w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s)
    (hconvd : ∀ x : Fin (n + 1) → ℂˣ, ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges (ψ.scale (-1)) abv μ w'.val
        (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x⁻¹) s)
    (Q Qd : (Fin (n + 1) → ℂˣ) → LaurentPolynomial ℂ)
    (hQ : ∀ x : Fin (n + 1) → ℂˣ, HasRationalContinuation q
      (corankOneIntegral ψ abv μ w.val
        (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x))
      (laurentToRatFunc (Q x) * essentialFactor P x))
    (hQd : ∀ x : Fin (n + 1) → ℂˣ, HasRationalContinuation q
      (corankOneIntegral (ψ.scale (-1)) abv μ w'.val
        (inverseSphericalWhittaker h'.conductor.1 h'.uniformizer q x⁻¹))
      (laurentToRatFunc (Qd x) * essentialFactor Pd x⁻¹))
    (hunit : ∀ x : Fin (n + 1) → ℂˣ, (∀ i, ‖(x i : ℂ)‖ = 1) →
      NormalizedFunctionalEquation q (∏ i, P.comp (C (x i : ℂ) * X))
        (∏ i, Pd.comp (C (((x i)⁻¹ : ℂˣ) : ℂ) * X)) ζ (c * (∏ i, x i) ^ m) e k
        (laurentToRatFunc (Q x) * essentialFactor P x)
        (laurentToRatFunc (Qd x) * essentialFactor Pd x⁻¹))
    (x : Fin (n + 1) → ℂˣ) :
    NormalizedFunctionalEquation q (∏ i, P.comp (C (x i : ℂ) * X))
      (∏ i, Pd.comp (C (((x i)⁻¹ : ℂˣ) : ℂ) * X)) ζ (c * (∏ i, x i) ^ m) e k
      (laurentToRatFunc (Q x) * essentialFactor P x)
      (laurentToRatFunc (Qd x) * essentialFactor Pd x⁻¹) := by
  have hq : 1 < q := h.one_lt_q
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  set DP := corankOneModelDenominatorProduct h π hπ ℓ w P with hDP
  set DPd := corankOneModelDenominatorProduct h' ρ hρ ℓ' w' Pd with hDPd
  have hcoef : ∀ (y : Fin (n + 1) → ℂˣ) (d : ℤ),
      (Q y).coeff d = torusPolynomialEvaluation (Fin (n + 1)) ℂ y (DP.coeff d).val :=
    fun y d => laurentNumerator_coeff_eq_specialized h π hπ ℓ hP w y (hconv y) (hQ y) d
  have hcoefd : ∀ (y : Fin (n + 1) → ℂˣ) (d : ℤ),
      (Qd y).coeff d = torusPolynomialEvaluation (Fin (n + 1)) ℂ y
        (torusPolynomialInversion (Fin (n + 1)) ℂ (DPd.coeff d).val) := by
    intro y d
    rw [torusPolynomialEvaluation_inversion]
    exact laurentNumerator_coeff_eq_specialized h' ρ hρ ℓ' hPd w' y⁻¹ (hconvd y) (hQd y) d
  let E : ℤ → TorusPolynomialAlgebra (Fin (n + 1)) ℂ := fun j =>
    algebraMap ℂ _ ((q : ℂ) ^ j) *
        torusPolynomialInversion (Fin (n + 1)) ℂ (DPd.coeff (-j)).val -
      algebraMap ℂ _ ((ζ : ℂ) ^ e * (c : ℂ)) *
        ((torusDeterminantUnit (Fin (n + 1)) ℂ ^ m :
          (TorusPolynomialAlgebra (Fin (n + 1)) ℂ)ˣ) : TorusPolynomialAlgebra (Fin (n + 1)) ℂ) *
        (DP.coeff (j - k)).val
  have hEval : ∀ (y : Fin (n + 1) → ℂˣ) (j : ℤ),
      torusPolynomialEvaluation (Fin (n + 1)) ℂ y (E j) =
        (q : ℂ) ^ j * (Qd y).coeff (-j) -
          ((ζ : ℂ) ^ e * ((c * (∏ i, y i) ^ m : ℂˣ) : ℂ)) * (Q y).coeff (j - k) := by
    intro y j
    simp only [E, map_sub, map_mul, AlgHom.commutes, hcoef, hcoefd]
    rw [algHom_apply_unit_zpow ℂ (torusPolynomialEvaluation (Fin (n + 1)) ℂ y)
      (torusDeterminantUnit (Fin (n + 1)) ℂ) m, torusPolynomialEvaluation_determinantUnit]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, Units.val_mul,
      Units.val_zpow_eq_zpow_val, Units.coe_prod]
    ring
  have hiff : ∀ y : Fin (n + 1) → ℂˣ,
      reflectLaurent q hq0 (Qd y) =
          (LaurentPolynomial.C ((ζ : ℂ) ^ e * ((c * (∏ i, y i) ^ m : ℂˣ) : ℂ)) *
            LaurentPolynomial.T k) * Q y ↔
        ∀ j, torusPolynomialEvaluation (Fin (n + 1)) ℂ y (E j) = 0 := by
    intro y
    constructor
    · intro hid j
      have hj := congrArg (fun L : LaurentPolynomial ℂ => L.coeff j) hid
      simp only [reflectLaurent_coeff, monomial_mul_laurent_coeff] at hj
      rw [hEval, hj, sub_self]
    · intro hz
      ext j
      rw [reflectLaurent_coeff, monomial_mul_laurent_coeff]
      have hj := hz j
      rw [hEval, sub_eq_zero] at hj
      exact hj
  have hE : ∀ j, E j = 0 := by
    intro j
    apply torusPolynomial_eq_zero_of_unitary_evaluations
    intro y hy
    exact (hiff y).mp (normalizedFE_cleared_laurent_identity hq
      (laurentToRatFunc_eq_algebraMap_prod_mul_essentialFactor hP y (Q y))
      (laurentToRatFunc_eq_algebraMap_prod_mul_essentialFactor hPd y⁻¹ (Qd y))
      (hunit y hy)) j
  apply normalizedFunctionalEquation_of_laurent_identity hq0
    (laurentToRatFunc_eq_algebraMap_prod_mul_essentialFactor hP x (Q x))
    (laurentToRatFunc_eq_algebraMap_prod_mul_essentialFactor hPd x⁻¹ (Qd x))
  exact (hiff x).mpr (fun j => by rw [hE j, map_zero])

end Extension

end Langlands.Conductor

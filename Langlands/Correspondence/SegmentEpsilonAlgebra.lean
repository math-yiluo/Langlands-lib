import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.Representation.RankinSelberg.RationalEvaluation
import Langlands.Representation.RankinSelberg.LanglandsFactors

/-!
# Rational-function algebra for segment-pair epsilon factors

Evaluation of finite products and of reflected L-ratios at regular points, the
reflection of an epsilon monomial, and the cancellation law: two gamma
expressions with the same nonzero L-polynomial and dual polynomials of constant
term `1` have the same epsilon monomial.
-/

noncomputable section

open Polynomial

namespace Langlands.RankinSelberg.RationalEvaluation

open LocalFactor

universe u uG uV

variable {K : Type u} [Field K] {z : K}

theorem RegularAt.prod {ι : Type*} (s : Finset ι) {f : ι → RatFunc K}
    (h : ∀ i ∈ s, RegularAt (f i) z) : RegularAt (∏ i ∈ s, f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (RegularAt.polynomial (z := z) (1 : K[X]))
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem eval_prod {ι : Type*} (s : Finset ι) {f : ι → RatFunc K}
    (h : ∀ i ∈ s, RegularAt (f i) z) :
    RatFunc.eval (RingHom.id K) z (∏ i ∈ s, f i) =
      ∏ i ∈ s, RatFunc.eval (RingHom.id K) z (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, RegularAt (f j) z := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      eval_mul (h i (Finset.mem_insert_self i s)) (RegularAt.prod s hs), ih hs]

variable {G : Type uG} [Group G] {ν : G →* Kˣ}

/-- The reflected L-ratio is regular at a nonzero point where the dual Euler
polynomial does not vanish at the reflected point. -/
theorem regularAt_rationalLRatio
    (A : WeilDeligneRepresentation.{u, uG, uV} K G ν) (I : Subgroup G) [I.Normal] (g : G)
    (c : Kˣ) (hz : z ≠ 0)
    (hd : (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval
      ((c : K) / z) ≠ 0) :
    RegularAt (WeilDeligne.rationalLRatio A I g c) z := by
  rw [WeilDeligne.rationalLRatio_eq, div_eq_mul_inv]
  exact (RegularAt.polynomial _).mul (RegularAt.inv (by
    rw [eval_aeval (regular_reflectedVariable c hz), eval_reflectedVariable c hz]
    exact hd))

/-- The value of the reflected L-ratio at a regular point. -/
theorem eval_rationalLRatio
    (A : WeilDeligneRepresentation.{u, uG, uV} K G ν) (I : Subgroup G) [I.Normal] (g : G)
    (c : Kˣ) (hz : z ≠ 0)
    (hd : (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval
      ((c : K) / z) ≠ 0) :
    RatFunc.eval (RingHom.id K) z (WeilDeligne.rationalLRatio A I g c) =
      (WeilDeligne.eulerPolynomial A I g).eval z /
        (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A) I g).eval
          ((c : K) / z) := by
  rw [WeilDeligne.rationalLRatio_eq, eval_div (RegularAt.polynomial _) (by
    rw [eval_aeval (regular_reflectedVariable c hz), eval_reflectedVariable c hz]
    exact hd), eval_aeval (regular_reflectedVariable c hz), eval_reflectedVariable c hz,
    RatFunc.eval_algebraMap]
  simp

end Langlands.RankinSelberg.RationalEvaluation

namespace Langlands.RankinSelberg

open LocalFactor

variable {K : Type*} [Field K]

/-- The reflection `X ↦ c / X` of the monomial `a X^m` is `(a c^m) X^(-m)`. -/
theorem subst_monomial (c : Kˣ) (a : K) (m : ℤ) :
    RationalReflection.subst c (RatFunc.C a * RatFunc.X ^ m) =
      RatFunc.C (a * (c : K) ^ m) * RatFunc.X ^ (-m) := by
  have h : RationalReflection.subst c (RatFunc.C a) = RatFunc.C a := by
    rw [← RatFunc.algebraMap_eq_C, AlgHom.commutes]
  rw [map_mul, map_zpow₀, h, RationalReflection.subst_X, RationalReflection.reflectedVariable,
    RatFunc.algebraMap_eq_C, div_zpow, map_mul, map_zpow₀, zpow_neg, div_eq_mul_inv]
  ring

/-- One direction of `monomial_mul_cancel`: the smaller exponent cannot be strictly
smaller. -/
private theorem exponent_eq_of_le {a b : K} {m n : ℤ} {P P' : K[X]} (ha : a ≠ 0)
    (hP : P.coeff 0 = 1) (hmn : m ≤ n)
    (h : RatFunc.C a * RatFunc.X ^ m * algebraMap K[X] (RatFunc K) P =
      RatFunc.C b * RatFunc.X ^ n * algebraMap K[X] (RatFunc K) P') :
    m = n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = m + k := ⟨(n - m).toNat, by omega⟩
  rw [zpow_add₀ RatFunc.X_ne_zero, zpow_natCast] at h
  have h2 : RatFunc.X ^ m * (RatFunc.C a * algebraMap K[X] (RatFunc K) P) =
      RatFunc.X ^ m * (RatFunc.C b * RatFunc.X ^ k * algebraMap K[X] (RatFunc K) P') := by
    linear_combination h
  have h3 := mul_left_cancel₀ (zpow_ne_zero m RatFunc.X_ne_zero) h2
  rw [← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_X, ← map_pow,
    ← map_mul, ← map_mul, ← map_mul] at h3
  have h4 := congrArg (fun Q : K[X] => Q.coeff 0) (RatFunc.algebraMap_injective K h3)
  simp only [coeff_C_mul, mul_assoc, coeff_X_pow_mul', hP, mul_one] at h4
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk]; simp
  · simp only [show ¬ (k ≤ 0) from by omega, ↓reduceIte, mul_zero] at h4
    exact absurd h4 ha

/-- Cancellation of monomials against polynomials of constant term `1`: if
`a X^m P = b X^n P'` with `a, b ≠ 0` and `P(0) = P'(0) = 1`, then `m = n` and
`a = b`. -/
theorem monomial_mul_cancel {a b : K} {m n : ℤ} {P P' : K[X]} (ha : a ≠ 0) (hb : b ≠ 0)
    (hP : P.coeff 0 = 1) (hP' : P'.coeff 0 = 1)
    (h : RatFunc.C a * RatFunc.X ^ m * algebraMap K[X] (RatFunc K) P =
      RatFunc.C b * RatFunc.X ^ n * algebraMap K[X] (RatFunc K) P') :
    m = n ∧ a = b := by
  have hmn : m = n := by
    rcases le_total m n with hle | hle
    · exact exponent_eq_of_le ha hP hle h
    · exact (exponent_eq_of_le hb hP' hle h.symm).symm
  subst hmn
  refine ⟨rfl, ?_⟩
  have h2 : RatFunc.X ^ m * (RatFunc.C a * algebraMap K[X] (RatFunc K) P) =
      RatFunc.X ^ m * (RatFunc.C b * algebraMap K[X] (RatFunc K) P') := by
    linear_combination h
  have h3 := mul_left_cancel₀ (zpow_ne_zero m RatFunc.X_ne_zero) h2
  rw [← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C, ← map_mul, ← map_mul] at h3
  have h4 := congrArg (fun Q : K[X] => Q.coeff 0) (RatFunc.algebraMap_injective K h3)
  simpa only [coeff_C_mul, hP, hP', mul_one] using h4

theorem prod_X_zpow {ι : Type*} (s : Finset ι) (m : ι → ℤ) :
    ∏ i ∈ s, (RatFunc.X : RatFunc K) ^ m i = RatFunc.X ^ (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ RatFunc.X_ne_zero]

/-- A double product of epsilon monomials is the epsilon monomial of the product
data. -/
theorem prod_rationalEpsilonMonomial {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι → κ → ℂˣ × ℤ) :
    ∏ i, ∏ j, (rationalEpsilonMonomial (e i j).1 (e i j).2 : RatFunc ℂ) =
      (rationalEpsilonMonomial (epsilonFactorProduct e).1 (epsilonFactorProduct e).2 :
        RatFunc ℂ) := by
  simp only [coe_rationalEpsilonMonomial, RatFunc.algebraMap_eq_C, Finset.prod_mul_distrib,
    epsilonFactorProduct, Units.coe_prod, map_prod, prod_X_zpow]

/-- **Cancellation of gamma expressions.** If two gamma expressions with the same
nonzero L-polynomial `P` agree, and both dual polynomials have constant term `1`,
then the epsilon monomials agree. -/
theorem rationalGammaExpression_cancel {δ c c' : ℂˣ} {m m' : ℤ} {P D D' : ℂ[X]}
    (hP : P ≠ 0) (hD : D.coeff 0 = 1) (hD' : D'.coeff 0 = 1)
    (h : rationalGammaExpression δ c m P D = rationalGammaExpression δ c' m' P D') :
    c = c' ∧ m = m' := by
  have hD0 : D ≠ 0 := fun h0 => by simp [h0] at hD
  have hD0' : D' ≠ 0 := fun h0 => by simp [h0] at hD'
  have hA : aeval (RationalReflection.reflectedVariable δ) D ≠ 0 := by
    rw [← RationalReflection.subst_polynomial]
    exact (map_ne_zero_iff _ (RationalReflection.equiv δ).injective).mpr
      (RatFunc.algebraMap_ne_zero hD0)
  have hA' : aeval (RationalReflection.reflectedVariable δ) D' ≠ 0 := by
    rw [← RationalReflection.subst_polynomial]
    exact (map_ne_zero_iff _ (RationalReflection.equiv δ).injective).mpr
      (RatFunc.algebraMap_ne_zero hD0')
  have hP0 : algebraMap ℂ[X] (RatFunc ℂ) P ≠ 0 := RatFunc.algebraMap_ne_zero hP
  unfold rationalGammaExpression at h
  rw [coe_rationalEpsilonMonomial, coe_rationalEpsilonMonomial, div_eq_div_iff hA hA'] at h
  have h2 : algebraMap ℂ[X] (RatFunc ℂ) P *
        (RatFunc.C (c : ℂ) * RatFunc.X ^ m * aeval (RationalReflection.reflectedVariable δ) D') =
      algebraMap ℂ[X] (RatFunc ℂ) P *
        (RatFunc.C (c' : ℂ) * RatFunc.X ^ m' *
          aeval (RationalReflection.reflectedVariable δ) D) := by
    simp only [RatFunc.algebraMap_eq_C] at h
    linear_combination h
  have h3 := congrArg (RationalReflection.subst δ) (mul_left_cancel₀ hP0 h2)
  rw [map_mul (RationalReflection.subst δ) (RatFunc.C (c : ℂ) * RatFunc.X ^ m),
    map_mul (RationalReflection.subst δ) (RatFunc.C (c' : ℂ) * RatFunc.X ^ m'),
    subst_monomial, subst_monomial, ← RationalReflection.subst_polynomial,
    ← RationalReflection.subst_polynomial, RationalReflection.subst_subst,
    RationalReflection.subst_subst] at h3
  obtain ⟨hm, hc⟩ := monomial_mul_cancel
    (mul_ne_zero c.ne_zero (zpow_ne_zero _ δ.ne_zero))
    (mul_ne_zero c'.ne_zero (zpow_ne_zero _ δ.ne_zero)) hD' hD h3
  have hm' : m = m' := neg_injective hm
  subst hm'
  exact ⟨Units.ext (mul_right_cancel₀ (zpow_ne_zero _ δ.ne_zero) hc), rfl⟩

end Langlands.RankinSelberg

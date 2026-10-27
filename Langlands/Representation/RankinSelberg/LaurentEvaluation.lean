import Langlands.Representation.RankinSelberg.RationalZeta
import Langlands.Representation.RankinSelberg.RationalContinuation

/-!
# Laurent evaluation at nonzero points and linear Laurent lifts

Laurent coefficients in the formal spectral variable `X = q^(-s)` can be
evaluated at every nonzero complex number. This file records that evaluation,
its exact relation to totalized evaluation of rational functions, and linear
Laurent lifts of trilinear families of rational functions whose denominators
are cleared by a fixed polynomial.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

/-- Evaluation of Laurent coefficients at a nonzero complex number. -/
def laurentEval (x : ℂˣ) : LaurentCoefficients →ₐ[ℂ] ℂ :=
  { LaurentPolynomial.eval₂ (RingHom.id ℂ) x with
    commutes' := fun c => by
      change LaurentPolynomial.eval₂ (RingHom.id ℂ) x
        (algebraMap ℂ LaurentCoefficients c) = c
      rw [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.eval₂_C]
      rfl }

theorem laurentEval_apply (x : ℂˣ) (a : LaurentCoefficients) :
    laurentEval x a = LaurentPolynomial.eval₂ (RingHom.id ℂ) x a := rfl

@[simp]
theorem laurentEval_T (x : ℂˣ) (m : ℤ) :
    laurentEval x (LaurentPolynomial.T m) = (x : ℂ) ^ m := by
  rw [laurentEval_apply, LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val]

@[simp]
theorem laurentEval_C (x : ℂˣ) (c : ℂ) :
    laurentEval x (LaurentPolynomial.C c) = c := by
  rw [laurentEval_apply, LaurentPolynomial.eval₂_C]
  rfl

@[simp]
theorem laurentEval_toLaurent (x : ℂˣ) (p : ℂ[X]) :
    laurentEval x (Polynomial.toLaurent p) = p.eval (x : ℂ) := by
  rw [laurentEval_apply, LaurentPolynomial.eval₂_toLaurent]
  rfl

theorem laurentEval_smul (x : ℂˣ) (c : ℂ) (a : LaurentCoefficients) :
    laurentEval x (c • a) = c * laurentEval x a := by
  rw [LaurentPolynomial.smul_eq_C_mul, map_mul, laurentEval_C]

/-- A quotient of polynomials whose denominator does not vanish at `z` is
regular at `z`, with the expected value. -/
private theorem regular_and_eval_div (z : ℂ) (N D : ℂ[X]) (hD : D.eval z ≠ 0) :
    (algebraMap ℂ[X] RationalFunctions N / algebraMap ℂ[X] RationalFunctions D).denom.eval z
        ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) z
          (algebraMap ℂ[X] RationalFunctions N / algebraMap ℂ[X] RationalFunctions D) =
        N.eval z / D.eval z := by
  have hD0 : D ≠ 0 := by
    rintro rfl
    simp at hD
  set R := algebraMap ℂ[X] RationalFunctions N / algebraMap ℂ[X] RationalFunctions D
  have hR : R.denom.eval z ≠ 0 := fun h =>
    hD (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd N D) h)
  refine ⟨hR, ?_⟩
  have hmul : R * algebraMap ℂ[X] RationalFunctions D = algebraMap ℂ[X] RationalFunctions N :=
    div_mul_cancel₀ _ (RatFunc.algebraMap_ne_zero hD0)
  have hden : (algebraMap ℂ[X] RationalFunctions D).denom.eval z ≠ 0 := by
    simp
  have he := congrArg (RatFunc.eval (RingHom.id ℂ) z) hmul
  rw [RatFunc.eval_mul (RingHom.id ℂ) z hR hden, RatFunc.eval_algebraMap,
    RatFunc.eval_algebraMap] at he
  rw [eq_div_iff hD]
  simpa using he

/-- The image of a Laurent polynomial is regular at every nonzero point. -/
theorem laurentToRatFunc_regular_and_eval (x : ℂˣ) (a : LaurentCoefficients) :
    (laurentToRatFunc a).denom.eval (x : ℂ) ≠ 0 ∧
      RatFunc.eval (RingHom.id ℂ) (x : ℂ) (laurentToRatFunc a) = laurentEval x a := by
  induction a using LaurentPolynomial.induction_on_mul_T with
  | mul_T p n =>
    have hX : ((X : ℂ[X]) ^ n).eval (x : ℂ) ≠ 0 := by
      simp
    have hrepr : laurentToRatFunc (Polynomial.toLaurent p * LaurentPolynomial.T (-(n : ℤ))) =
        algebraMap ℂ[X] RationalFunctions p / algebraMap ℂ[X] RationalFunctions (X ^ n) := by
      rw [map_mul, laurentToRatFunc_toLaurent, laurentToRatFunc_T, zpow_neg, zpow_natCast,
        div_eq_mul_inv, map_pow, RatFunc.algebraMap_X]
    obtain ⟨hreg, heval⟩ := regular_and_eval_div (x : ℂ) p (X ^ n) hX
    refine ⟨hrepr ▸ hreg, ?_⟩
    rw [hrepr, heval, map_mul, laurentEval_toLaurent, laurentEval_T]
    simp [div_eq_mul_inv]

theorem laurentToRatFunc_regular (x : ℂˣ) (a : LaurentCoefficients) :
    (laurentToRatFunc a).denom.eval (x : ℂ) ≠ 0 :=
  (laurentToRatFunc_regular_and_eval x a).1

theorem eval_laurentToRatFunc (x : ℂˣ) (a : LaurentCoefficients) :
    RatFunc.eval (RingHom.id ℂ) (x : ℂ) (laurentToRatFunc a) = laurentEval x a :=
  (laurentToRatFunc_regular_and_eval x a).2

/-- Evaluation bridge with a separate denominator guard on `R` only. -/
theorem laurentEval_eq_of_laurentToRatFunc_eq (x : ℂˣ) {a : LaurentCoefficients} {P : ℂ[X]}
    {R : RationalFunctions}
    (ha : laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * R)
    (hR : R.denom.eval (x : ℂ) ≠ 0) :
    laurentEval x a = P.eval (x : ℂ) * RatFunc.eval (RingHom.id ℂ) (x : ℂ) R := by
  have hP : (algebraMap ℂ[X] RationalFunctions P).denom.eval (x : ℂ) ≠ 0 := by
    simp
  rw [← eval_laurentToRatFunc, ha, RatFunc.eval_mul (RingHom.id ℂ) (x : ℂ) hP hR,
    RatFunc.eval_algebraMap]
  rfl

/-- The spectral point as a unit. -/
def spectralUnit {q : ℕ} (hq : 0 < q) (s : ℂ) : ℂˣ :=
  Units.mk0 (spectralPoint q s)
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hq.ne')))

@[simp]
theorem coe_spectralUnit {q : ℕ} (hq : 0 < q) (s : ℂ) :
    (spectralUnit hq s : ℂ) = spectralPoint q s := rfl

theorem spectralPoint_sub_one_sub {q : ℕ} (hq : 0 < q) (s : ℂ) :
    spectralPoint q (1 - s) = ((q : ℂ))⁻¹ * (spectralPoint q s)⁻¹ := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [spectralPoint, Complex.cpow_neg, neg_sub, inv_inv]
  rw [Complex.cpow_sub _ _ hq0, Complex.cpow_one, div_eq_mul_inv, mul_comm]

/-- The embedding of Laurent coefficients in rational functions commutes with
complex scalar multiplication. -/
theorem laurentToRatFunc_smul (c : ℂ) (a : LaurentCoefficients) :
    laurentToRatFunc (c • a) = c • laurentToRatFunc a := by
  rw [LaurentPolynomial.smul_eq_C_mul, map_mul, RatFunc.smul_eq_C_mul]
  congr 1
  simp [laurentToRatFunc]

/-- The embedding as a complex-linear map. -/
def laurentToRatFuncLinear : LaurentCoefficients →ₗ[ℂ] RationalFunctions where
  toFun := laurentToRatFunc
  map_add' := map_add laurentToRatFunc
  map_smul' := laurentToRatFunc_smul

@[simp]
theorem laurentToRatFuncLinear_apply (a : LaurentCoefficients) :
    laurentToRatFuncLinear a = laurentToRatFunc a := rfl

section Lift

universe uM uM' uS

variable {M : Type uM} {M' : Type uM'} {S : Type uS}
  [AddCommMonoid M] [Module ℂ M] [AddCommMonoid M'] [Module ℂ M'] [AddCommMonoid S] [Module ℂ S]

/-- Pointwise choice of the Laurent coefficients clearing a value. -/
private def liftValue (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    (f : M) (f' : M') (Φ : S) : LaurentCoefficients :=
  Classical.choose (h f f' Φ)

private theorem liftValue_spec (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    (f : M) (f' : M') (Φ : S) :
    laurentToRatFunc (liftValue P D h f f' Φ) = algebraMap ℂ[X] RationalFunctions P * D f f' Φ :=
  Classical.choose_spec (h f f' Φ)

private theorem eq_liftValue (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    {f : M} {f' : M'} {Φ : S} {a : LaurentCoefficients}
    (ha : laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ) :
    liftValue P D h f f' Φ = a :=
  laurentToRatFunc_injective ((liftValue_spec P D h f f' Φ).trans ha.symm)

/-- The Laurent lift for fixed first and second arguments. -/
private def liftInner (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    (f : M) (f' : M') : S →ₗ[ℂ] LaurentCoefficients where
  toFun Φ := liftValue P D h f f' Φ
  map_add' Φ₁ Φ₂ := eq_liftValue P D h (by
    rw [map_add, liftValue_spec, liftValue_spec, map_add, mul_add])
  map_smul' c Φ := eq_liftValue P D h (by
    rw [RingHom.id_apply, laurentToRatFunc_smul, liftValue_spec, map_smul, mul_smul_comm])

private theorem liftInner_apply (P : ℂ[X])
    (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    (f : M) (f' : M') (Φ : S) : liftInner P D h f f' Φ = liftValue P D h f f' Φ := rfl

/-- The Laurent lift for a fixed first argument. -/
private def liftMiddle (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    (f : M) : M' →ₗ[ℂ] S →ₗ[ℂ] LaurentCoefficients where
  toFun f' := liftInner P D h f f'
  map_add' f'₁ f'₂ := LinearMap.ext fun Φ => eq_liftValue P D h (by
    rw [LinearMap.add_apply, liftInner_apply, liftInner_apply, map_add, liftValue_spec,
      liftValue_spec, map_add, LinearMap.add_apply, mul_add])
  map_smul' c f' := LinearMap.ext fun Φ => eq_liftValue P D h (by
    rw [LinearMap.smul_apply, liftInner_apply, RingHom.id_apply, laurentToRatFunc_smul,
      liftValue_spec, map_smul, LinearMap.smul_apply, mul_smul_comm])

private theorem liftMiddle_apply (P : ℂ[X])
    (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    (f : M) (f' : M') (Φ : S) : liftMiddle P D h f f' Φ = liftValue P D h f f' Φ := rfl

/-- The Laurent lift of a trilinear family of rational functions whose values
are cleared by `P`. Linearity follows from injectivity of `laurentToRatFunc`. -/
def laurentLift (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ) :
    M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] LaurentCoefficients where
  toFun f := liftMiddle P D h f
  map_add' f₁ f₂ := LinearMap.ext fun f' => LinearMap.ext fun Φ => eq_liftValue P D h (by
    rw [LinearMap.add_apply, LinearMap.add_apply, liftMiddle_apply, liftMiddle_apply, map_add,
      liftValue_spec, liftValue_spec, map_add, LinearMap.add_apply, LinearMap.add_apply,
      mul_add])
  map_smul' c f := LinearMap.ext fun f' => LinearMap.ext fun Φ => eq_liftValue P D h (by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, liftMiddle_apply, RingHom.id_apply,
      laurentToRatFunc_smul, liftValue_spec, map_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, mul_smul_comm])

theorem laurentLift_spec (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    (f : M) (f' : M') (Φ : S) :
    laurentToRatFunc (laurentLift P D h f f' Φ) =
      algebraMap ℂ[X] RationalFunctions P * D f f' Φ :=
  liftValue_spec P D h f f' Φ

theorem eq_laurentLift (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    {f : M} {f' : M'} {Φ : S} {a : LaurentCoefficients}
    (ha : laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ) :
    laurentLift P D h f f' Φ = a :=
  eq_liftValue P D h ha

theorem laurentLift_eq_iff (P : ℂ[X]) (D : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (h : ∀ f f' Φ, ∃ a : LaurentCoefficients,
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ)
    (f : M) (f' : M') (Φ : S) (a : LaurentCoefficients) :
    laurentLift P D h f f' Φ = a ↔
      laurentToRatFunc a = algebraMap ℂ[X] RationalFunctions P * D f f' Φ :=
  ⟨fun ha => ha ▸ laurentLift_spec P D h f f' Φ, eq_laurentLift P D h⟩

end Lift

section Composition

universe uM uM' uS uN uN' uU uA uB

variable {M : Type uM} {M' : Type uM'} {S : Type uS} {N : Type uN} {N' : Type uN'}
  {U : Type uU} {A : Type uA} {B : Type uB}
  [AddCommMonoid M] [Module ℂ M] [AddCommMonoid M'] [Module ℂ M'] [AddCommMonoid S] [Module ℂ S]
  [AddCommMonoid N] [Module ℂ N] [AddCommMonoid N'] [Module ℂ N'] [AddCommMonoid U] [Module ℂ U]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]

/-- Postcomposition of a trilinear map with a linear map. -/
def trilinearPostcomp (φ : A →ₗ[ℂ] B) (T : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] A) :
    M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] B :=
  T.compr₂ (LinearMap.compRight ℂ φ)

@[simp]
theorem trilinearPostcomp_apply (φ : A →ₗ[ℂ] B) (T : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] A)
    (f : M) (f' : M') (Φ : S) : trilinearPostcomp φ T f f' Φ = φ (T f f' Φ) := rfl

/-- Precomposition of a trilinear map with linear maps in each argument. -/
def trilinearPrecomp (T : N →ₗ[ℂ] N' →ₗ[ℂ] U →ₗ[ℂ] A) (a : M →ₗ[ℂ] N) (b : M' →ₗ[ℂ] N')
    (c : S →ₗ[ℂ] U) : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] A :=
  (T.compl₁₂ a b).compr₂ (LinearMap.lcomp ℂ A c)

@[simp]
theorem trilinearPrecomp_apply (T : N →ₗ[ℂ] N' →ₗ[ℂ] U →ₗ[ℂ] A) (a : M →ₗ[ℂ] N)
    (b : M' →ₗ[ℂ] N') (c : S →ₗ[ℂ] U) (f : M) (f' : M') (Φ : S) :
    trilinearPrecomp T a b c f f' Φ = T (a f) (b f') (c Φ) := rfl

end Composition

end Langlands.RankinSelberg

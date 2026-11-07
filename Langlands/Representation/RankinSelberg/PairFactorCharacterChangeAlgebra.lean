import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuationFamily
import Langlands.Representation.RankinSelberg.LaurentTransport
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Monomial transport of normalized functional equations

If two families of integrals differ by fixed nonzero monomials `α X^a` and
`β X^b` in the spectral variable `X = q^(-s)`, their value sets span the same
Laurent module, and a normalized functional equation for the first family gives
one for the second with an explicitly changed epsilon monomial.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial RationalEvaluation

/-- At a nonzero point, a nonzero monomial multiple is regular exactly when the
rational function is. -/
theorem regularAt_C_mul_X_zpow_mul_iff {z : ℂ} (hz : z ≠ 0) {c : ℂ} (hc : c ≠ 0) (m : ℤ)
    (R : RationalFunctions) :
    RegularAt (RatFunc.C c * RatFunc.X ^ m * R) z ↔ RegularAt R z := by
  have hX : RatFunc.eval (RingHom.id ℂ) z (RatFunc.X : RationalFunctions) ≠ 0 := by
    rw [RatFunc.eval_X]
    exact hz
  have hM : ∀ (c : ℂ) (m : ℤ),
      RegularAt (RatFunc.C c * (RatFunc.X : RationalFunctions) ^ m) z :=
    fun c m => (regularAt_C c z).mul (RegularAt.zpow hX m)
  constructor
  · intro h
    have hR : R = RatFunc.C c⁻¹ * RatFunc.X ^ (-m) * (RatFunc.C c * RatFunc.X ^ m * R) := by
      rw [show RatFunc.C c⁻¹ * RatFunc.X ^ (-m) * (RatFunc.C c * RatFunc.X ^ m * R) =
          (RatFunc.C c⁻¹ * RatFunc.C c) * (RatFunc.X ^ (-m) * RatFunc.X ^ m) * R by ring,
        ← map_mul, inv_mul_cancel₀ hc, map_one,
        ← zpow_add₀ (RatFunc.X_ne_zero : (RatFunc.X : RationalFunctions) ≠ 0),
        neg_add_cancel, zpow_zero, one_mul, one_mul]
    rw [hR]
    exact (hM _ _).mul h
  · intro h
    exact (hM c m).mul h

/-- A normalized functional equation is transported by nonzero monomial
multiples `α X^a` of the original and `β X^b` of the dual continuation, when the
new epsilon monomial `c' X^m'` satisfies `m' + a = m - b` and
`c' α = c β q^(-b)`. -/
theorem NormalizedFunctionalEquation.monomial_transport {q : ℕ} (hq : 0 < q)
    {P Pdual : Polynomial ℂ} {ζ c : ℂˣ} {e : ℕ} {m : ℤ} {R Rdual : RationalFunctions}
    (h : NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual)
    {c' : ℂˣ} {m' : ℤ} (α β : ℂˣ) (a b : ℤ) (hm : m' + a = m - b)
    (hc : (c' : ℂ) * α = c * β * (q : ℂ) ^ (-b)) :
    NormalizedFunctionalEquation q P Pdual ζ c' e m'
      (RatFunc.C (α : ℂ) * RatFunc.X ^ a * R) (RatFunc.C (β : ℂ) * RatFunc.X ^ b * Rdual) := by
  intro s hR' hRd'
  have hX := spectralPoint_ne_zero_of_pos hq s
  have hXd := spectralPoint_ne_zero_of_pos hq (1 - s)
  have hR := (regularAt_C_mul_X_zpow_mul_iff hX α.ne_zero a R).mp hR'
  have hRd := (regularAt_C_mul_X_zpow_mul_iff hXd β.ne_zero b Rdual).mp hRd'
  have he := h s hR hRd
  rw [eval_C_mul_X_zpow_mul hX hR, eval_C_mul_X_zpow_mul hXd hRd]
  unfold epsilonMonomial at he ⊢
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have key : (β : ℂ) * spectralPoint q (1 - s) ^ b * ((c : ℂ) * spectralPoint q s ^ m) =
      (c' : ℂ) * spectralPoint q s ^ m' * ((α : ℂ) * spectralPoint q s ^ a) := by
    rw [spectralPoint_sub_one_sub hq, mul_zpow, inv_zpow', inv_zpow']
    calc (β : ℂ) * ((q : ℂ) ^ (-b) * spectralPoint q s ^ (-b)) *
          ((c : ℂ) * spectralPoint q s ^ m) =
        ((c : ℂ) * β * (q : ℂ) ^ (-b)) * (spectralPoint q s ^ (-b) * spectralPoint q s ^ m) := by
          ring
      _ = ((c' : ℂ) * α) * (spectralPoint q s ^ m' * spectralPoint q s ^ a) := by
          rw [hc, ← zpow_add₀ hX, ← zpow_add₀ hX, show -b + m = m' + a by omega]
      _ = _ := by ring
  linear_combination ((β : ℂ) * spectralPoint q (1 - s) ^ b) * he +
    ((ζ : ℂ) ^ e * P.eval (spectralPoint q s) *
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R) * key

section Families

variable {q : ℕ} {V W M₁ M₁' M₂ M₂' : Type*}
  {I₁ : M₁ → M₁' → ℂ → ℂ} {I₂ : M₂ → M₂' → ℂ → ℂ}
  {c₁ : V → M₁} {c₁' : W → M₁'} {c₂ : V → M₂} {c₂' : W → M₂'} {T : V → V}

/-- Value sets of two integral families related by one nonzero monomial,
through surjective parametrizations by vectors, span the same Laurent module. -/
theorem zetaSpan_values_eq_of_monomial (hq : 0 < q)
    (hc₁ : Function.Surjective c₁) (hc₁' : Function.Surjective c₁')
    (hc₂ : Function.Surjective c₂) (hc₂' : Function.Surjective c₂')
    (hT : Function.Surjective T) (α : ℂˣ) (a : ℤ)
    (hI : ∀ v w s, I₂ (c₂ v) (c₂' w) s = α * spectralPoint q s ^ a * I₁ (c₁ (T v)) (c₁' w) s) :
    zetaSpan {R | ∃ x y, HasRationalContinuation q (I₁ x y) R} =
      zetaSpan {R | ∃ x y, HasRationalContinuation q (I₂ x y) R} := by
  apply zetaSpan_eq_of_monomial_mul α a
  · rintro R ⟨x, y, hR⟩
    obtain ⟨u, rfl⟩ := hc₁ x
    obtain ⟨w, rfl⟩ := hc₁' y
    obtain ⟨v, rfl⟩ := hT u
    refine ⟨c₂ v, c₂' w, ?_⟩
    have h := hR.monomial_mul hq α a
    convert h using 1
    funext s
    exact hI v w s
  · rintro R ⟨x, y, hR⟩
    obtain ⟨v, rfl⟩ := hc₂ x
    obtain ⟨w, rfl⟩ := hc₂' y
    refine ⟨c₁ (T v), c₁' w, ?_⟩
    have h := hR.monomial_mul hq (↑α⁻¹) (-a)
    convert h using 1
    funext s
    have hX : spectralPoint q s ^ a ≠ 0 := zpow_ne_zero _ (spectralPoint_ne_zero_of_pos hq s)
    rw [hI v w s, zpow_neg, Units.val_inv_eq_inv_val]
    field_simp

variable {D₁ : M₁ → M₁' → ℂ → ℂ} {D₂ : M₂ → M₂' → ℂ → ℂ}

/-- The functional-equation clause of a fixed block transfers along monomial
relations of both the original and the dual integrals. -/
theorem functionalEquation_transfer_of_monomial (hq : 0 < q)
    (hc₂ : Function.Surjective c₂) (hc₂' : Function.Surjective c₂')
    (α β : ℂˣ) (a b : ℤ)
    (hI : ∀ v w s, I₂ (c₂ v) (c₂' w) s = α * spectralPoint q s ^ a * I₁ (c₁ (T v)) (c₁' w) s)
    (hD : ∀ v w s, D₂ (c₂ v) (c₂' w) s = β * spectralPoint q s ^ b * D₁ (c₁ (T v)) (c₁' w) s)
    {P Pdual : Polynomial ℂ} {ζ c c' : ℂˣ} {e : ℕ} {m m' : ℤ} (hm : m' + a = m - b)
    (hc : (c' : ℂ) * α = c * β * (q : ℂ) ^ (-b))
    (h : ∀ x y, ∃ R Rdual : RationalFunctions,
      HasRationalContinuation q (I₁ x y) R ∧ HasRationalContinuation q (D₁ x y) Rdual ∧
        NormalizedFunctionalEquation q P Pdual ζ c e m R Rdual) :
    ∀ x y, ∃ R Rdual : RationalFunctions,
      HasRationalContinuation q (I₂ x y) R ∧ HasRationalContinuation q (D₂ x y) Rdual ∧
        NormalizedFunctionalEquation q P Pdual ζ c' e m' R Rdual := by
  intro x y
  obtain ⟨v, rfl⟩ := hc₂ x
  obtain ⟨w, rfl⟩ := hc₂' y
  obtain ⟨R, Rd, hR, hRd, hN⟩ := h (c₁ (T v)) (c₁' w)
  refine ⟨_, _, ?_, ?_, hN.monomial_transport hq α β a b hm hc⟩
  · convert hR.monomial_mul hq α a using 1
    funext s
    exact hI v w s
  · convert hRd.monomial_mul hq β b using 1
    funext s
    exact hD v w s

end Families

end Langlands.RankinSelberg

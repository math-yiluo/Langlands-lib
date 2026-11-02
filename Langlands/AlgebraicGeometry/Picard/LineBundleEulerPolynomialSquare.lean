import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomial

/-! # Euler polynomials determined by squared Euler characteristics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- A rational polynomial whose square agrees with `c^2 X^(2g)` at every positive
integer, and which is nonnegative at `1`, is `c X^g`. -/
theorem polynomial_eq_C_mul_X_pow_of_sq_eval (P : ℚ[X]) (g : ℕ) (c : ℚ) (hc : 0 ≤ c)
    (hsq : ∀ k : ℕ, 0 < k → P.eval (k : ℚ) ^ 2 = c ^ 2 * (k : ℚ) ^ (2 * g))
    (hpos : 0 ≤ P.eval 1) :
    P = C c * X ^ g := by
  have hQ : P ^ 2 - (C c * X ^ g) ^ 2 = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((k + 1 : ℕ) : ℚ))
      (fun a b hab => by simpa using hab) fun k => ?_
    simp only [Set.mem_ofPred_eq, IsRoot, eval_sub, eval_pow, eval_mul, eval_C, eval_X]
    rw [hsq (k + 1) k.succ_pos, mul_pow, ← pow_mul, mul_comm g 2, sub_self]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sub_eq_zero.mp hQ) with h | h
  · exact h
  · have h1 : P.eval 1 = -c := by simp [h]
    have hc0 : c = 0 := by linarith
    rw [h, hc0]
    simp

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- **Euler coefficient from squared Euler characteristics.** Let `L` be a line bundle on
a proper Noetherian separated scheme over a field `K`, of topological Krull dimension at
most `g`. If `χ(L^k)^2 = c^2 k^(2g)` for every positive `k` and `χ(L) ≥ 0`, then the
degree-`g` coefficient of the actual Euler polynomial of `L` is `c`. -/
theorem lineBundleEulerPolynomial_coeff_eq_of_eulerCharacteristic_sq
    [IsNoetherian X] [X.IsSeparated] (L : LineBundle X) (g : ℕ)
    (hX : topologicalKrullDim X ≤ g) (c : ℕ)
    (hsq : ∀ k : ℕ, 0 < k → ∀ h : HasFiniteCohomology f (tensorPow L.obj k),
      eulerCharacteristic f (tensorPow L.obj k) h ^ 2 = (c : ℤ) ^ 2 * (k : ℤ) ^ (2 * g))
    (hpos : ∀ h : HasFiniteCohomology f (tensorPow L.obj 1),
      0 ≤ eulerCharacteristic f (tensorPow L.obj 1) h) :
    (lineBundleEulerPolynomial f L g).coeff g = c := by
  have hP := polynomial_eq_C_mul_X_pow_of_sq_eval (lineBundleEulerPolynomial f L g) g c
    (Nat.cast_nonneg c)
    (fun k hk => by
      rw [lineBundleEulerPolynomial_eval f L g hX k
        (lineBundleTensorPow_hasFiniteCohomology f L k)]
      exact_mod_cast hsq k hk _)
    (by
      have := lineBundleEulerPolynomial_eval f L g hX 1
        (lineBundleTensorPow_hasFiniteCohomology f L 1)
      rw [Nat.cast_one] at this
      rw [this]
      exact_mod_cast hpos _)
  rw [hP]
  simp

end Langlands.AlgebraicGeometry.Picard

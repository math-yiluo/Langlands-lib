import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fin.Tuple.Basic

/-! # Homogeneous polynomial laws on a module -/

noncomputable section

namespace Langlands.LinearAlgebra

open scoped BigOperators

variable {R : Type*} [CommSemiring R]
  {E : Type*} [AddCommMonoid E] [Module R E]

/-- Polynomiality and homogeneity on every finite tuple, with no chosen basis. -/
def HasHomogeneousPolynomialLaw (δ : E → R) (d : ℕ) : Prop :=
  ∀ (n : ℕ) (a : Fin n → E),
    ∃ P : MvPolynomial (Fin n) R, P.IsHomogeneous d ∧
      ∀ x : Fin n → R, MvPolynomial.eval x P = δ (∑ i, x i • a i)

/-- Homogeneous multivariate polynomials scale by their total degree. -/
theorem homogeneous_eval_smul {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ R} {d : ℕ} (hP : P.IsHomogeneous d)
    (c : R) (x : σ → R) :
    MvPolynomial.eval (c • x) P = c ^ d * MvPolynomial.eval x P := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmd := hP (MvPolynomial.mem_support_iff.mp hm)
  change m.weight (fun _ => 1) = d at hmd
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum] at hmd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hmd]
  ac_rfl

namespace HasHomogeneousPolynomialLaw

variable {δ ε : E → R} {d : ℕ}

/-- The polynomial-law premise implies the expected scalar homogeneity. -/
theorem map_smul (hδ : HasHomogeneousPolynomialLaw δ d) (c : R) (a : E) :
    δ (c • a) = c ^ d * δ a := by
  obtain ⟨P, hP, he⟩ := hδ 1 ![a]
  have hs := homogeneous_eval_smul hP c (1 : Fin 1 → R)
  simpa [he, Fin.sum_univ_one] using hs

/-- Positive-degree homogeneous laws vanish at the origin. -/
theorem map_zero (hδ : HasHomogeneousPolynomialLaw δ d) (hd : d ≠ 0) : δ 0 = 0 := by
  simpa [hd] using hδ.map_smul (0 : R) (0 : E)

/-- Precomposition with a linear map preserves the law. -/
theorem comp_linearMap {F : Type*} [AddCommMonoid F] [Module R F]
    (hδ : HasHomogeneousPolynomialLaw δ d) (f : F →ₗ[R] E) :
    HasHomogeneousPolynomialLaw (δ ∘ f) d := by
  intro n a
  obtain ⟨P, hP, he⟩ := hδ n (fun i => f (a i))
  refine ⟨P, hP, ?_⟩
  intro x
  simpa using he x

end HasHomogeneousPolynomialLaw

/-- Scalar homogeneity makes the rational extension of an integral lattice
unique whenever every vector admits a nonzero integral denominator. -/
theorem homogeneousLaw_eq_of_integer_lattice
    {V M : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup M]
    {δ ε : V → ℚ} {d : ℕ}
    (hδ : HasHomogeneousPolynomialLaw δ d)
    (hε : HasHomogeneousPolynomialLaw ε d)
    (i : M →+ V)
    (hden : ∀ a : V, ∃ n : ℕ, n ≠ 0 ∧ ∃ m : M, (n : ℚ) • a = i m)
    (hi : ∀ m : M, δ (i m) = ε (i m)) : δ = ε := by
  funext a
  obtain ⟨n, hn, m, hm⟩ := hden a
  apply mul_left_cancel₀ (pow_ne_zero d (Nat.cast_ne_zero.mpr hn : (n : ℚ) ≠ 0))
  rw [← hδ.map_smul, ← hε.map_smul, hm, hi]

end Langlands.LinearAlgebra

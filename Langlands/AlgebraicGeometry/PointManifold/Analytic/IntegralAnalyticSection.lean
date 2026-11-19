import Langlands.AlgebraicGeometry.PointManifold.Analytic.ComplexPolynomialGrowth
import Langlands.AlgebraicGeometry.PointTopology.NormedFinitePointProper
import Mathlib.Algebra.MvPolynomial.Funext

/-! # Analytic sections of finite algebras are algebraic -/

open scoped BigOperators

namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

private theorem exists_norm_eval_le {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℂ) :
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ x, ‖MvPolynomial.eval x p‖ ≤ C * max 1 ‖x‖ ^ d := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    exact ⟨‖c‖, 0, norm_nonneg _, by simp⟩
  | add p q hp hq =>
    obtain ⟨C, d, hC, hp⟩ := hp
    obtain ⟨D, e, hD, hq⟩ := hq
    refine ⟨C + D, max d e, add_nonneg hC hD, fun x => ?_⟩
    rw [map_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (hp x).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (le_max_left _ _) (le_max_left _ _)) hC)
    · exact (hq x).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (le_max_left _ _) (le_max_right _ _)) hD)
  | mul_X p i hp =>
    obtain ⟨C, d, hC, hp⟩ := hp
    refine ⟨C, d + 1, hC, fun x => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hp x) ((norm_le_pi_norm x i).trans (le_max_right _ _)) (norm_nonneg _)
      (mul_nonneg hC (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))

section

variable {ι A : Type*} [Fintype ι] [CommRing A] [Algebra ℂ A]
variable [Algebra (MvPolynomial ι ℂ) A]

private theorem exists_norm_section_eval_le
    (s : (ι → ℂ) → A →ₐ[ℂ] ℂ)
    (hs : ∀ x p, s x (algebraMap (MvPolynomial ι ℂ) A p) = MvPolynomial.eval x p)
    (a : A) (ha : IsIntegral (MvPolynomial ι ℂ) a) :
    ∃ (C : ℝ) (d : ℕ), ∀ x, ‖s x a‖ ≤ C * max 1 ‖x‖ ^ d := by
  obtain ⟨P, hP, hroot⟩ := ha
  choose C d hC h using fun j : ℕ => exists_norm_eval_le (P.coeff j)
  let J := Finset.range P.natDegree
  let D := J.sup d
  refine ⟨1 + ∑ j ∈ J, C j, D, fun x => ?_⟩
  have hpx : P.eval₂ (MvPolynomial.eval x) (s x a) = 0 := by
    have he : (s x).toRingHom.comp (algebraMap (MvPolynomial ι ℂ) A) =
        MvPolynomial.eval x := RingHom.ext (hs x)
    change P.eval₂ (MvPolynomial.eval x) ((s x).toRingHom a) = 0
    simpa only [Polynomial.hom_eval₂, he, map_zero] using
      congrArg (s x).toRingHom hroot
  refine (PointTopology.norm_root_le_one_add_sum P hP (MvPolynomial.eval x) hpx).trans ?_
  rw [add_mul, one_mul, Finset.sum_mul]
  refine add_le_add (one_le_pow₀ (le_max_left _ _)) (Finset.sum_le_sum fun j hj => ?_)
  exact (h j x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (le_max_left _ _) (Finset.le_sup hj)) (hC j))

/-- An analytic family of points over the identity of complex affine space on
a module-finite algebra is induced by a homomorphism to the polynomial base. -/
theorem exists_algHom_of_integral_analytic_section [Module.Finite (MvPolynomial ι ℂ) A]
    (s : (ι → ℂ) → A →ₐ[ℂ] ℂ)
    (hs : ∀ x p, s x (algebraMap (MvPolynomial ι ℂ) A p) = MvPolynomial.eval x p)
    (hanalytic : ∀ a x, AnalyticAt ℂ (fun y => s y a) x) :
    ∃ φ : A →ₐ[MvPolynomial ι ℂ] MvPolynomial ι ℂ,
      ∀ x a, MvPolynomial.eval x (φ a) = s x a := by
  have hpoly (a : A) : ∃ p : MvPolynomial ι ℂ, ∀ x, MvPolynomial.eval x p = s x a := by
    obtain ⟨C, d, hC⟩ := exists_norm_section_eval_le s hs a (Algebra.IsIntegral.isIntegral a)
    exact exists_mvPolynomial_of_analytic_polynomialGrowth (hanalytic a) hC
  choose p hp using hpoly
  refine ⟨
    { toFun := p
      map_one' := MvPolynomial.funext fun x => by rw [hp, map_one, map_one]
      map_mul' := fun a b => MvPolynomial.funext fun x => by simp only [hp, map_mul]
      map_zero' := MvPolynomial.funext fun x => by rw [hp, map_zero, map_zero]
      map_add' := fun a b => MvPolynomial.funext fun x => by simp only [hp, map_add]
      commutes' := fun r => MvPolynomial.funext fun x => by
        rw [hp, hs, Algebra.algebraMap_self_apply] }, fun x a => hp a x⟩

end

end Langlands.AlgebraicGeometry.PointManifold.Analytic

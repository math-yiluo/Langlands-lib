import Langlands.LinearAlgebra.ComplexPolynomialRoots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Dynamics.Newton
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

open Polynomial Algebra

namespace Langlands

universe u

private lemma squarefree_dvd_of_eval_zero {g p : ℂ[X]} (hg : Squarefree g)
    (hp : ∀ a, g.eval a = 0 → p.eval a = 0) : g ∣ p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  apply (IsAlgClosed.splits g).dvd_of_roots_le_roots hg.ne_zero
  apply (Multiset.le_iff_subset
    (Polynomial.nodup_roots (PerfectField.separable_iff_squarefree.mpr hg))).mpr
  intro a ha
  exact (mem_roots hp0).mpr (hp a ((mem_roots hg.ne_zero).mp ha))

/-- Polynomial roots of invertible finite-dimensional complex endomorphisms. -/
theorem complexPolynomialRoots : ComplexPolynomialRoots.{u} := by
  classical
  intro V _ _ _ A hA n hn
  let m := minpoly ℂ A
  have hm0 : m ≠ 0 := minpoly.ne_zero (LinearMap.isIntegral A)
  have hmzero : m.eval 0 ≠ 0 := by
    simpa only [m, coeff_zero_eq_eval_zero] using A.minpoly_coeff_zero_of_injective
      ((Module.End.isUnit_iff A).mp hA).injective
  obtain ⟨g, k, hg, hgm, hmg⟩ := exists_squarefree_dvd_pow_of_ne_zero hm0
  choose r hr using fun a : ℂ => IsAlgClosed.exists_pow_nat_eq a hn
  let q : ℂ[X] := Lagrange.interpolate m.roots.toFinset id r
  have hq (a : ℂ) (ha : m.eval a = 0) : q.eval a = r a := by
    apply Lagrange.eval_interpolate_at_node r (Function.injective_id.injOn)
    exact Multiset.mem_toFinset.mpr ((mem_roots hm0).mpr ha)
  have hgq : g ∣ q ^ n - X := by
    apply squarefree_dvd_of_eval_zero hg
    intro a ha
    have hma : m.eval a = 0 := eval_eq_zero_of_dvd_of_eval_eq_zero hgm ha
    simp [hq a hma, hr]
  have hmq : IsCoprime m q := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ m q).mpr
    intro a
    by_cases ha : m.eval a = 0
    · right
      simp only [coe_aeval_eq_eval]
      rw [hq a ha]
      intro hra
      have ha0 : a = 0 := by simpa [hra, hn.ne'] using (hr a).symm
      exact hmzero (ha0 ▸ ha)
    · left
      simpa only [coe_aeval_eq_eval] using ha
  let B := Algebra.adjoin ℂ ({A} : Set (Module.End ℂ V))
  let a : B := ⟨A, self_mem_adjoin_singleton ℂ A⟩
  have hm : aeval a m = 0 := by
    apply Subtype.ext
    simp [a, m, coe_aeval_mk_apply]
  have hnil : IsNilpotent ((aeval a q) ^ n - a) := by
    refine ⟨k, ?_⟩
    have h := aeval_eq_zero_of_dvd_aeval_eq_zero
      (hmg.trans (pow_dvd_pow_of_dvd hgq k)) hm
    simpa only [map_pow, map_sub, aeval_X] using h
  have hunit : IsUnit (aeval a q) := by
    obtain ⟨s, t, hst⟩ := hmq
    apply IsUnit.of_mul_eq_one_right (aeval a t)
    have h := congrArg (aeval a) hst
    simpa only [map_add, map_mul, map_one, hm, mul_zero, zero_add] using h
  have hnunit : IsUnit (n : B) := by
    have hc : IsUnit (n : ℂ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
    simpa only [map_natCast] using hc.map (algebraMap ℂ B)
  have hderiv : IsUnit (aeval (aeval a q) (derivative (X ^ n - C a : B[X]))) := by
    simpa [derivative_X_pow] using hnunit.mul (hunit.pow (n - 1))
  obtain ⟨b, hb, -⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero
    (P := (X ^ n - C a : B[X])) (x := aeval a q) (by simpa using hnil) hderiv
  have hbpow : b ^ n = a := sub_eq_zero.mp (by simpa using hb.2)
  obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval ℂ A b
  refine ⟨p, ?_⟩
  have h := congrArg (fun z : B => (z : Module.End ℂ V)) hbpow
  simpa [← hp, a] using h

end Langlands

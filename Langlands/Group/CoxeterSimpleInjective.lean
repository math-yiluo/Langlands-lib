import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Distinct simple reflections via the geometric representation

Every Coxeter matrix acts on `B → ℂ` by the transposed geometric reflections
`f ↦ f - 2 f(i) a_i`, where `a_i j = -cos(π / M i j)`. These operators satisfy
the Coxeter relations, so they lift to every Coxeter system, and distinct
indices give distinct operators. Mathlib lists this distinctness as a TODO.
-/

namespace Langlands.Group.RelativeWeylIndexing

universe u v

variable {B : Type u} {W : Type v} [Group W]

open Complex Polynomial

noncomputable section

/-- The half-angle root of unity `exp(π i / m)`. -/
private def halfRoot (m : ℕ) : ℂ := exp (Real.pi * I / m)

/-- The geometric coefficient `-cos(π / M i j)`, written through `halfRoot`. -/
private def geomCoeff (M : CoxeterMatrix B) (i j : B) : ℂ :=
  -(halfRoot (M i j) + (halfRoot (M i j))⁻¹) / 2

/-- The transposed geometric reflection `f ↦ f - 2 f(i) a_i`. -/
private def geomRefl (M : CoxeterMatrix B) (i : B) : Module.End ℂ (B → ℂ) :=
  LinearMap.id - (LinearMap.proj i : (B → ℂ) →ₗ[ℂ] ℂ).smulRight
    (fun j => 2 * geomCoeff M i j)

variable {M : CoxeterMatrix B}

private theorem geomRefl_apply (i : B) (f : B → ℂ) (j : B) :
    geomRefl M i f j = f j - f i * (2 * geomCoeff M i j) := by
  simp [geomRefl]

private theorem halfRoot_ne_zero (m : ℕ) : halfRoot m ≠ 0 := exp_ne_zero _

private theorem geomCoeff_self (i : B) : geomCoeff M i i = 1 := by
  have h : halfRoot 1 = -1 := by
    simp [halfRoot, exp_pi_mul_I]
  rw [geomCoeff, M.diagonal, h]
  norm_num

private theorem geomCoeff_symm (i j : B) : geomCoeff M i j = geomCoeff M j i := by
  rw [geomCoeff, geomCoeff, M.symmetric]

private theorem geomCoeff_of_two {i j : B} (h : M i j = 2) : geomCoeff M i j = 0 := by
  have h2 : halfRoot 2 = I := by
    have e : (Real.pi : ℂ) * I / ((2 : ℕ) : ℂ) = (Real.pi : ℂ) / 2 * I := by
      push_cast
      ring
    rw [halfRoot, e, exp_pi_div_two_mul_I]
  rw [geomCoeff, h, h2]
  simp

private theorem geomRefl_mul_self (i : B) : geomRefl M i * geomRefl M i = 1 := by
  refine LinearMap.ext fun f => funext fun j => ?_
  simp only [Module.End.mul_apply, geomRefl_apply, Module.End.one_apply, geomCoeff_self]
  ring

private theorem geomRefl_comm {i j : B} (h1 : geomCoeff M i j = 0)
    (h2 : geomCoeff M j i = 0) :
    geomRefl M i * geomRefl M j = geomRefl M j * geomRefl M i := by
  refine LinearMap.ext fun f => funext fun k => ?_
  simp only [Module.End.mul_apply, geomRefl_apply, h1, h2]
  ring

/-- The product of two reflections satisfies a cubic relation. -/
private theorem geomRefl_cubic (i j : B) :
    let A := geomRefl M i * geomRefl M j
    let t := 4 * geomCoeff M i j ^ 2 - 2
    (A * A - t • A + 1) * (A - 1) = 0 := by
  intro A t
  have hji : geomCoeff M j i = geomCoeff M i j := geomCoeff_symm j i
  refine LinearMap.ext fun f => funext fun k => ?_
  simp only [A, t, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply, geomRefl_apply,
    geomCoeff_self, hji, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  ring

/-- The cubic factors of a primitive `m`-th root of unity divide `X ^ m - 1`. -/
private theorem cubic_dvd {m : ℕ} (hm : 3 ≤ m) (c : ℂ)
    (hc : c = -(halfRoot m + (halfRoot m)⁻¹) / 2) :
    (X ^ 2 - C (4 * c ^ 2 - 2) * X + 1) * (X - 1) ∣ (X ^ m - 1 : ℂ[X]) := by
  set h := halfRoot m with hh
  set ζ := h ^ 2 with hζ
  have hprim : IsPrimitiveRoot ζ m := by
    have he : ζ = exp (2 * Real.pi * I / m) := by
      rw [hζ, hh, halfRoot, ← exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [he]
    exact isPrimitiveRoot_exp m (by omega)
  have h0 : h ≠ 0 := halfRoot_ne_zero m
  have hζ0 : ζ ≠ 0 := pow_ne_zero _ h0
  have ht : 4 * c ^ 2 - 2 = ζ + ζ⁻¹ := by
    rw [hc, hζ]
    field_simp
    ring
  have hfac : (X ^ 2 - C (4 * c ^ 2 - 2) * X + 1 : ℂ[X]) = (X - C ζ) * (X - C ζ⁻¹) := by
    have hprod : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
    rw [ht]
    have : (X - C ζ) * (X - C ζ⁻¹) = X ^ 2 - C (ζ + ζ⁻¹) * X + C (ζ * ζ⁻¹) := by
      simp only [C_add, C_mul]
      ring
    rw [this, hprod, C_1]
  have hne1 : ζ ≠ 1 := hprim.ne_one (by omega)
  have hinv1 : ζ⁻¹ ≠ 1 := inv_ne_one.mpr hne1
  have hneinv : ζ ≠ ζ⁻¹ := by
    intro he
    have hsq : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [he]
      exact mul_inv_cancel₀ hζ0
    have hdvd := (hprim.pow_eq_one_iff_dvd 2).mp hsq
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hroot : ∀ μ : ℂ, μ ^ m = 1 → (X - C μ) ∣ (X ^ m - 1 : ℂ[X]) := by
    intro μ hμ
    rw [dvd_iff_isRoot]
    simp [IsRoot, hμ]
  have hz : ζ ^ m = 1 := hprim.pow_eq_one
  have hzi : ζ⁻¹ ^ m = 1 := by rw [inv_pow, hz, inv_one]
  have hcop : ∀ a b : ℂ, a ≠ b → IsCoprime (X - C a) (X - C b) := fun a b hab =>
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
  rw [hfac]
  have h1 : (X - C ζ) * (X - C ζ⁻¹) ∣ (X ^ m - 1 : ℂ[X]) :=
    (hcop _ _ hneinv).mul_dvd (hroot _ hz) (hroot _ hzi)
  have h2 : (X - 1 : ℂ[X]) ∣ X ^ m - 1 := by
    simpa using hroot 1 (one_pow m)
  have hc : IsCoprime ((X - C ζ) * (X - C ζ⁻¹)) (X - 1 : ℂ[X]) := by
    have a1 := hcop ζ 1 hne1
    have a2 := hcop ζ⁻¹ 1 hinv1
    rw [C_1] at a1 a2
    exact a1.mul_left a2
  exact hc.mul_dvd h1 h2

private theorem geomRefl_pow_of_three {i j : B} (hm : 3 ≤ M i j) :
    (geomRefl M i * geomRefl M j) ^ M i j = 1 := by
  obtain ⟨r, hr⟩ := cubic_dvd hm (geomCoeff M i j) rfl
  set A := geomRefl M i * geomRefl M j with hA
  have hc : (A * A - (4 * geomCoeff M i j ^ 2 - 2) • A + 1) * (A - 1) = 0 :=
    geomRefl_cubic i j
  generalize 4 * geomCoeff M i j ^ 2 - 2 = t at hc hr
  have hq : aeval A ((X ^ 2 - C t * X + 1) * (X - 1)) = 0 := by
    simp only [map_mul, map_sub, map_add, map_pow, aeval_X, aeval_C, map_one]
    rw [sq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact hc
  have h := congrArg (aeval A) hr
  rw [map_mul, hq, zero_mul, map_sub, map_pow, aeval_X, map_one] at h
  exact sub_eq_zero.mp h

private theorem geomRefl_isLiftable : M.IsLiftable (geomRefl M) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [M.diagonal, pow_one, geomRefl_mul_self]
  · have h1 : M i j ≠ 1 := M.off_diagonal i j hij
    rcases (by omega : M i j = 0 ∨ M i j = 2 ∨ 3 ≤ M i j) with h0 | h2 | h3
    · rw [h0, pow_zero]
    · have c1 : geomCoeff M i j = 0 := geomCoeff_of_two h2
      have c2 : geomCoeff M j i = 0 := by rw [← geomCoeff_symm]; exact c1
      have hcomm := geomRefl_comm c1 c2
      rw [h2, sq]
      calc geomRefl M i * geomRefl M j * (geomRefl M i * geomRefl M j)
          = geomRefl M i * (geomRefl M j * geomRefl M i) * geomRefl M j := by
            simp only [mul_assoc]
        _ = geomRefl M i * (geomRefl M i * geomRefl M j) * geomRefl M j := by
            rw [← hcomm]
        _ = (geomRefl M i * geomRefl M i) * (geomRefl M j * geomRefl M j) := by
            simp only [mul_assoc]
        _ = 1 := by rw [geomRefl_mul_self, geomRefl_mul_self, one_mul]
    · exact geomRefl_pow_of_three h3

/-- Distinct indices of a Coxeter system give distinct simple reflections. -/
theorem simple_injective (cs : CoxeterSystem M W) : Function.Injective cs.simple := by
  classical
  intro i j hij
  by_contra hne
  have h := congrArg (cs.lift ⟨geomRefl M, geomRefl_isLiftable⟩) hij
  rw [cs.lift_apply_simple, cs.lift_apply_simple] at h
  have hv := congrArg (fun A : Module.End ℂ (B → ℂ) => A (Pi.single i 1) i) h
  simp only [geomRefl_apply, Pi.single_eq_same, geomCoeff_self] at hv
  rw [Pi.single_eq_of_ne (Ne.symm hne)] at hv
  norm_num at hv

end

end Langlands.Group.RelativeWeylIndexing

import Mathlib.Algebra.Ring.GeomSum
import Langlands.Representation.RankinSelberg.PoleOrderAtZeroArithmetic

/-!
# Pole order and residue-degree substitution

For a denominator polynomial in `q_E^(-s)`, rewriting it in the variable
`q_F^(-s)` substitutes `X ^ f` for `X`, where `q_E = q_F ^ f`. The multiplicity
of `1`, hence the pole order at `s = 0`, is unchanged for positive `f` over `ℂ`.
-/

namespace Langlands.RankinSelberg

open Polynomial

/-- Composition with `X ^ f` preserves multiplicity at `1` when `f` is nonzero
in the coefficient domain. -/
theorem rootMultiplicity_one_comp_X_pow {R : Type*} [CommRing R] [IsDomain R]
    (P : R[X]) {f : ℕ} (hf : (f : R) ≠ 0) :
    (P.comp (X ^ f)).rootMultiplicity 1 = P.rootMultiplicity 1 := by
  by_cases hP : P = 0
  · simp [hP]
  obtain ⟨Q, hPQ, hQ⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP 1
  have hQ1 : (Q.comp (X ^ f)).eval 1 ≠ 0 := by
    intro he
    apply hQ
    apply dvd_iff_isRoot.mpr
    simpa only [IsRoot, eval_comp, eval_pow, eval_X, one_pow] using he
  let m := P.rootMultiplicity 1
  let H : R[X] := ∑ i ∈ Finset.range f, X ^ i
  have hH1 : H.eval 1 ≠ 0 := by
    simpa [H] using hf
  have hXf : (X ^ f - C 1 : R[X]) = H * (X - C 1) := by
    simpa only [H, map_one] using (geom_sum_mul (X : R[X]) f).symm
  have hcomp : P.comp (X ^ f) = (H ^ m * Q.comp (X ^ f)) * (X - C 1) ^ m := by
    calc
      P.comp (X ^ f) = ((X - C 1) ^ m * Q).comp (X ^ f) :=
        congrArg (·.comp (X ^ f)) hPQ
      _ = _ := by
        rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, hXf, mul_pow]
        ac_rfl
  have hA1 : (H ^ m * Q.comp (X ^ f)).eval 1 ≠ 0 := by
    rw [eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero m hH1) hQ1
  have hA : H ^ m * Q.comp (X ^ f) ≠ 0 := fun h => hA1 (by rw [h, eval_zero])
  rw [hcomp, rootMultiplicity_mul_X_sub_C_pow hA, rootMultiplicity_eq_zero hA1, zero_add]

/-- Expressing a complex local denominator in the base-field variable preserves
its pole order at zero, provided the residue degree is positive. -/
theorem lPolynomialPoleOrderAtZero_comp_X_pow (P : ℂ[X]) {f : ℕ} (hf : 0 < f) :
    lPolynomialPoleOrderAtZero (P.comp (X ^ f)) = lPolynomialPoleOrderAtZero P :=
  rootMultiplicity_one_comp_X_pow P (Nat.cast_ne_zero.mpr hf.ne')

end Langlands.RankinSelberg

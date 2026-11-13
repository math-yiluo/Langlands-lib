import Langlands.AlgebraicGeometry.LangWeil.Stepanov.ResultantDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.Separable

/-!
# The discriminant good set of a plane curve

Let `fh : F[X][Y]` be irreducible with nonzero `Y`-derivative, `n` its `Y`-degree and `m` a bound
for the `X`-degrees of its coefficients. The resultant `Δ = Res_Y(fh, ∂fh/∂Y)` (Sylvester sizes
`n`, `n - 1`) is a nonzero polynomial in `X` of degree at most `(2n - 1) m`, and at every `x`
with `Δ(x) ≠ 0` the specialisation `fh(x, Y)` keeps `Y`-degree `n` and is separable.
-/

open Polynomial

universe u

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

/-- The coefficients of the `Y`-derivative obey the same `X`-degree bound as those of `fh`. -/
theorem natDegree_coeff_derivative_le {R : Type u} [CommRing R] (fh : Polynomial (Polynomial R))
    (m : ℕ) (hm : ∀ i, (fh.coeff i).natDegree ≤ m) (k : ℕ) :
    ((derivative fh).coeff k).natDegree ≤ m := by
  rw [coeff_derivative]
  have h : ((k : Polynomial R) + 1) = C ((k : R) + 1) := by simp
  rw [h]
  exact (natDegree_mul_C_le _ _).trans (hm _)

/-- Over a field, a nonzero resultant (for any admissible Sylvester sizes, not both zero)
forces coprimality. -/
theorem isCoprime_of_resultant_ne_zero {K : Type u} [Field K] (f g : K[X]) (a b : ℕ)
    (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ b) (hab : a ≠ 0 ∨ b ≠ 0)
    (h : f.resultant g a b ≠ 0) : IsCoprime f g := by
  obtain ⟨p, q, -, -, e⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg hab
  refine ⟨C (f.resultant g a b)⁻¹ * p, C (f.resultant g a b)⁻¹ * q, ?_⟩
  calc C (f.resultant g a b)⁻¹ * p * f + C (f.resultant g a b)⁻¹ * q * g
      = C (f.resultant g a b)⁻¹ * (f * p + g * q) := by ring
    _ = 1 := by rw [e, ← C_mul, inv_mul_cancel₀ h, C_1]

/-- **Discriminant good set.** For `fh : F[X][Y]` irreducible with nonzero `Y`-derivative and
coefficients of `X`-degree at most `m`, there is a nonzero `Δ : F[X]` of degree at most
`(2 n - 1) m`, `n = natDegree fh`, such that for every `x` with `Δ(x) ≠ 0` the specialisation
`fh(x, Y)` has `Y`-degree `n` and is separable. One may take `Δ = Res_Y(fh, ∂fh/∂Y)`. -/
theorem exists_goodSet_discriminant {F : Type u} [Field F] (fh : Polynomial (Polynomial F))
    (m : ℕ) (hirr : Irreducible fh) (hsep : Polynomial.derivative fh ≠ 0)
    (hm : ∀ i, (fh.coeff i).natDegree ≤ m) :
    ∃ Δ : Polynomial F, Δ ≠ 0 ∧ Δ.natDegree ≤ (2 * fh.natDegree - 1) * m ∧
      ∀ x : F, Δ.eval x ≠ 0 →
        (fh.map (Polynomial.evalRingHom x)).natDegree = fh.natDegree ∧
        (fh.map (Polynomial.evalRingHom x)).Separable := by
  have hn : fh.natDegree ≠ 0 := by
    intro h0
    apply hsep
    rw [eq_C_of_natDegree_eq_zero h0, derivative_C]
  have hfh0 : fh ≠ 0 := by
    rintro rfl
    exact hn natDegree_zero
  refine ⟨resultant fh (derivative fh) fh.natDegree (fh.natDegree - 1), ?_, ?_, ?_⟩
  · -- `Δ ≠ 0`: pass to the fraction field `K = F(X)`, where `fh` stays irreducible (Gauss).
    let K := FractionRing (Polynomial F)
    let φ : Polynomial F →+* K := algebraMap (Polynomial F) K
    have hφ : Function.Injective φ := IsFractionRing.injective (Polynomial F) K
    have hirrK : Irreducible (fh.map φ) :=
      ((hirr.isPrimitive hn).irreducible_iff_irreducible_map_fraction_map (K := K)).1 hirr
    have hderK : derivative (fh.map φ) ≠ 0 := by
      rw [derivative_map]
      exact (Polynomial.map_ne_zero_iff hφ).2 hsep
    have hcop : IsCoprime (fh.map φ) (derivative (fh.map φ)) :=
      (separable_def _).1 ((separable_iff_derivative_ne_zero hirrK).2 hderK)
    have hdegK : (fh.map φ).natDegree = fh.natDegree := natDegree_map_eq_of_injective hφ fh
    have hdK : (derivative (fh.map φ)).natDegree ≤ fh.natDegree - 1 :=
      (natDegree_derivative_le _).trans (by rw [hdegK])
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hdK
    have hres : φ (resultant fh (derivative fh) fh.natDegree (fh.natDegree - 1)) =
        (fh.map φ).coeff fh.natDegree ^ k * resultant (fh.map φ) (derivative (fh.map φ)) := by
      rw [← resultant_map_map, ← derivative_map, hk,
        resultant_add_right_deg (f := fh.map φ) (g := derivative (fh.map φ)) (m := fh.natDegree)
          (n := (derivative (fh.map φ)).natDegree) k le_rfl, hdegK]
    have hlc : (fh.map φ).coeff fh.natDegree ≠ 0 := by
      rw [coeff_map, coeff_natDegree]
      exact (map_ne_zero_iff φ hφ).2 (leadingCoeff_ne_zero.2 hfh0)
    intro h0
    have h1 := hres
    rw [h0, map_zero] at h1
    exact mul_ne_zero (pow_ne_zero _ hlc) (resultant_ne_zero _ _ hcop) h1.symm
  · -- Degree bound from the Sylvester column count.
    have h := resultant_natDegree_le fh (derivative fh) fh.natDegree (fh.natDegree - 1) m m hm
      (natDegree_coeff_derivative_le fh m hm)
    refine h.trans (le_of_eq ?_)
    have e : 2 * fh.natDegree - 1 = (fh.natDegree - 1) + fh.natDegree := by omega
    rw [e, add_mul]
  · intro x hx
    have hpos : 0 < fh.degree := by
      rw [← natDegree_pos_iff_degree_pos]
      exact Nat.pos_of_ne_zero hn
    have hlcx : (fh.leadingCoeff).eval x ≠ 0 := by
      intro h0
      apply hx
      rw [resultant_deriv hpos, eval_mul, eval_mul, h0, mul_zero, zero_mul]
    have hdegx : (fh.map (evalRingHom x)).natDegree = fh.natDegree :=
      natDegree_map_of_leadingCoeff_ne_zero (evalRingHom x) (by simpa using hlcx)
    refine ⟨hdegx, ?_⟩
    rw [separable_def]
    refine isCoprime_of_resultant_ne_zero _ _ fh.natDegree (fh.natDegree - 1) hdegx.le
      ((natDegree_derivative_le _).trans (by rw [hdegx])) (Or.inl hn) ?_
    rw [derivative_map, resultant_map_map]
    simpa using hx

end Langlands.AlgebraicGeometry.LangWeil.Stepanov

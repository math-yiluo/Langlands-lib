import Langlands.Representation.Archimedean.RealLeviChartIntegralStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Ordered block exponents for normalized principal series -/

noncomputable section

universe u

namespace Langlands.Archimedean

open RealLeviChart Langlands.GeneralLinear
open scoped BigOperators

set_option autoImplicit false

variable {c : ℕ} (size : Fin c → ℕ)

/-- The half exponent of a block determinant in normalized upper parabolic induction. -/
def blockHalfExponent (i : Fin c) : ℝ :=
  (((∑ j ∈ Finset.univ.filter (fun j => i < j), size j : ℕ) : ℝ) -
    ((∑ j ∈ Finset.univ.filter (fun j => j < i), size j : ℕ) : ℝ)) / 2

private theorem sum_before_eq_start (i : Fin c) :
    (∑ j ∈ Finset.univ.filter (fun j => j < i), size j) = start size i := by
  unfold start
  refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro a _ b _ h
    exact Fin.ext h
  · intro a ha
    have h := Finset.mem_range.mp ha
    exact ⟨⟨a, h.trans i.isLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  · intro a _
    simp only [dite_eq_left a.isLt]

theorem blockHalfExponent_eq_rank (i : Fin c) :
    blockHalfExponent size i = (((∑ j, size j : ℕ) : ℝ) - size i) / 2 - start size i := by
  have hin : i ∉ Finset.univ.filter (fun j : Fin c => i < j) := by simp
  have ht : Finset.univ.filter (fun j : Fin c => ¬j < i) =
      insert i (Finset.univ.filter (fun j : Fin c => i < j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_lt]
    rw [le_iff_eq_or_lt, eq_comm]
  have hsum := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j < i) size
  rw [ht, Finset.sum_insert hin, sum_before_eq_start size i] at hsum
  have hcast : (∑ j, (size j : ℝ)) = (start size i : ℝ) + size i +
      ∑ j ∈ Finset.univ.filter (fun j => i < j), (size j : ℝ) := by
    exact_mod_cast (hsum.symm.trans (Nat.add_assoc _ _ _).symm)
  unfold blockHalfExponent
  rw [sum_before_eq_start]
  push_cast
  rw [hcast]
  ring

/-- The pairwise determinant formula for the outer half modulus, regrouped by block. -/
theorem sqrt_pairwiseBlockModulus (d : Fin c → ℝ) (hd : ∀ i, 0 < d i) :
    Real.sqrt (∏ i : Fin c, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      d i ^ size j / d j ^ size i) =
      ∏ i : Fin c, d i ^ blockHalfExponent size i := by
  have hswap :
      (∏ i : Fin c, ∏ j ∈ Finset.univ.filter (fun j => i < j), d j ^ size i) =
        ∏ j : Fin c, ∏ i ∈ Finset.univ.filter (fun i => i < j), d j ^ size i :=
    Finset.prod_comm' (fun _ _ => by simp)
  simp_rw [Finset.prod_div_distrib]
  rw [hswap, ← Finset.prod_div_distrib]
  simp_rw [Finset.prod_pow_eq_pow_sum, ← Real.rpow_natCast]
  simp_rw [← Real.rpow_sub (hd _)]
  rw [Real.sqrt_prod _ (fun i _ => Real.rpow_nonneg (hd i).le _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (hd i).le, blockHalfExponent]
  congr 1
  ring

variable (𝕜 : Type u) [RCLike 𝕜]

/-- The principal-series character separates into the internal block characters and
the extra powers of the diagonal norms prescribed by the outer block exponents. -/
theorem principalSeriesCharacter_eq_blockProduct
    (χ : ℕ → 𝕜ˣ → ℂ) (χblock : Fin c → ℕ → 𝕜ˣ → ℂ)
    (hχ : ∀ (i : Fin c) (j : Fin (size i)), χ (pos size i j) = χblock i j)
    (a : Fin (∑ i, size i) → 𝕜ˣ) :
    principalSeriesCharacter 𝕜 (∑ i, size i) χ a =
      ∏ i : Fin c, principalSeriesCharacter 𝕜 (size i) (χblock i) (fun j => a (pos size i j)) *
        ∏ j : Fin (size i),
          ((‖(a (pos size i j) : 𝕜)‖ ^ Module.finrank ℝ 𝕜 : ℝ) : ℂ) ^
            (blockHalfExponent size i : ℂ) := by
  rw [principalSeriesCharacter, ← Equiv.prod_comp finSigmaFinEquiv, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [principalSeriesCharacter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  change χ (pos size i j) _ * _ = _
  rw [hχ i j, mul_assoc, ← Complex.cpow_add]
  · congr 2
    change (((∑ i, size i : ℕ) : ℂ) - 1) / 2 - ((pos size i j : ℕ) : ℂ) = _
    rw [blockHalfExponent_eq_rank, val_pos]
    push_cast
    ring
  · apply Complex.ofReal_ne_zero.mpr
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (a (pos size i j)).ne_zero)

/-- The normalized local determinant of the diagonal part in one block. -/
def blockDiagonalAbs (a : Fin (∑ i, size i) → 𝕜ˣ) (i : Fin c) : ℝ :=
  ‖(Iwasawa.diagonalUnits (fun j => a (pos size i j))).val.det‖ ^
    Module.finrank ℝ 𝕜

theorem blockDiagonalAbs_eq_prod (a : Fin (∑ i, size i) → 𝕜ˣ) (i : Fin c) :
    blockDiagonalAbs size 𝕜 a i =
      ∏ j : Fin (size i), ‖(a (pos size i j) : 𝕜)‖ ^ Module.finrank ℝ 𝕜 := by
  rw [blockDiagonalAbs, Iwasawa.diagonalUnits_val, Matrix.det_diagonal, norm_prod, Finset.prod_pow]

private theorem prod_rpow {J : Type*} (s : Finset J) (x : J → ℝ)
    (hx : ∀ j, 0 ≤ x j) (r : ℝ) :
    (∏ j ∈ s, x j) ^ r = ∏ j ∈ s, x j ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj hs =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj,
      Real.mul_rpow (hx j) (Finset.prod_nonneg fun i _ => hx i), hs]

/-- The normalized full torus character is the product of the inner torus
characters times the positive half of the outer block modulus. -/
theorem principalSeriesCharacter_eq_outerHalf_mul_inner
    (χ : ℕ → 𝕜ˣ → ℂ) (χblock : Fin c → ℕ → 𝕜ˣ → ℂ)
    (hχ : ∀ (i : Fin c) (j : Fin (size i)), χ (pos size i j) = χblock i j)
    (a : Fin (∑ i, size i) → 𝕜ˣ) :
    principalSeriesCharacter 𝕜 (∑ i, size i) χ a =
      (Real.sqrt (∏ i : Fin c, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        blockDiagonalAbs size 𝕜 a i ^ size j / blockDiagonalAbs size 𝕜 a j ^ size i) : ℂ) *
      ∏ i : Fin c, principalSeriesCharacter 𝕜 (size i) (χblock i) (fun j => a (pos size i j)) := by
  have hpos (i : Fin c) : 0 < blockDiagonalAbs size 𝕜 a i := by
    rw [blockDiagonalAbs_eq_prod]
    exact Finset.prod_pos fun j _ =>
      pow_pos (norm_pos_iff.mpr (a (pos size i j)).ne_zero) _
  rw [principalSeriesCharacter_eq_blockProduct size 𝕜 χ χblock hχ,
    sqrt_pairwiseBlockModulus size _ hpos, Complex.ofReal_prod, mul_comm, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [blockDiagonalAbs_eq_prod, prod_rpow _ _ (fun j => pow_nonneg (norm_nonneg _) _)]
  simp only [Complex.ofReal_prod, Complex.ofReal_cpow (pow_nonneg (norm_nonneg _) _)]

end Langlands.Archimedean

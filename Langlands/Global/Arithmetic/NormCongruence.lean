import Langlands.Global.Arithmetic.CyclotomicSymbol
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Analysis.Polynomial.Basic

/-! # Elementary facts on norms of number field elements

The field norm `N_{K/ℚ}(t + α)` is positive for all large rational `t`, and the norm of an
algebraic integer congruent to `1` modulo `n` is congruent to `1` modulo `n`. A rational
integer congruent to `1` modulo a high power of `ℓ` has trivial cyclotomic symbol at `ℓ`.
-/

noncomputable section

open NumberField Filter

namespace Langlands.Global.CyclotomicSymbol

section Positivity

variable {K : Type*} [Field K] [NumberField K]

/-- `N_{K/ℚ}(t + α)` is the characteristic polynomial of multiplication by `-α` at `t`. -/
theorem norm_algebraMap_add (t : ℚ) (α : K) :
    Algebra.norm ℚ (algebraMap ℚ K t + α) =
      (Algebra.lmul ℚ K (-α)).charpoly.eval t := by
  rw [LinearMap.eval_charpoly, Algebra.norm_apply]
  congr 1
  rw [map_neg, sub_neg_eq_add, map_add, AlgHom.commutes]

/-- The norm `N_{K/ℚ}(t + α)` is positive for all large rational `t`. -/
theorem eventually_norm_algebraMap_add_pos (α : K) :
    ∀ᶠ t in atTop, 0 < Algebra.norm ℚ (algebraMap ℚ K t + α) := by
  set P := (Algebra.lmul ℚ K (-α)).charpoly
  have hmonic : P.Monic := LinearMap.charpoly_monic _
  have hdeg : 0 < P.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, LinearMap.charpoly_natDegree]
    exact Module.finrank_pos
  have htend := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg P hdeg
    (by rw [hmonic.leadingCoeff]; exact zero_le_one)
  filter_upwards [htend.eventually_gt_atTop 0] with t ht
  rw [norm_algebraMap_add]
  exact ht

/-- For `T > 0`, some `α + k T` with `k ∈ ℕ` has positive norm. -/
theorem exists_norm_add_nsmul_pos (α : K) {T : ℚ} (hT : 0 < T) :
    ∃ k : ℕ, 0 < Algebra.norm ℚ (α + algebraMap ℚ K (k * T)) := by
  obtain ⟨k, hk⟩ := ((tendsto_natCast_atTop_atTop.atTop_mul_const hT).eventually
    (eventually_norm_algebraMap_add_pos α)).exists
  refine ⟨k, ?_⟩
  rw [add_comm]
  exact hk

end Positivity

section Congruence

variable {K : Type*} [Field K] [NumberField K]

/-- If an algebraic integer is `≡ 1 mod n`, so is its norm. -/
theorem intNorm_sub_one_dvd (n : ℕ) (α β : 𝓞 K) (h : α = 1 + (n : 𝓞 K) * β) :
    (n : ℤ) ∣ Algebra.norm ℤ α - 1 := by
  classical
  let b := RingOfIntegers.basis K
  have hz : ((n : ℕ) : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) (ZMod n)) = 0 := by
    rw [← Matrix.diagonal_natCast, ZMod.natCast_self, Matrix.diagonal_zero]
  have key : (Int.castRingHom (ZMod n)) (Algebra.norm ℤ α) = 1 := by
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det, h, map_add, map_one, map_mul,
      map_natCast, map_add, map_one, map_mul, map_natCast, hz, zero_mul, add_zero,
      Matrix.det_one]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, sub_eq_zero]
  exact key

end Congruence

section Symbol

variable (m : ℕ) [NeZero m]

/-- A rational integer `≡ 1 mod ℓ^{r+1}`, with `ℓ^r` the `ℓ`-part of `m`, has trivial
cyclotomic symbol at `ℓ`. -/
theorem ratLocalSymbol_intCast_eq_one (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (z : ℤ) (hz : (z : ℚ) ≠ 0)
    (h : (ℓ : ℤ) ^ (m.factorization ℓ + 1) ∣ z - 1) :
    ratLocalSymbol m ℓ (Units.mk0 (z : ℚ) hz) = 1 := by
  rw [ratLocalSymbol, MonoidHom.comp_apply]
  have hnorm : ‖((Units.map (Rat.castHom ℚ_[ℓ]).toMonoidHom (Units.mk0 (z : ℚ) hz) : ℚ_[ℓ]ˣ) :
      ℚ_[ℓ]) - 1‖ ≤ (ℓ : ℝ) ^ (-((m.factorization ℓ + 1 : ℕ) : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd (p := ℓ) (z - 1) (m.factorization ℓ + 1)).2
      (by exact_mod_cast h)
    simpa using this
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  apply localSymbol_eq_one
  · refine hnorm.trans (zpow_le_zpow_right₀ hℓ1.le ?_)
    push_cast
    linarith
  · refine hnorm.trans_lt ?_
    apply zpow_lt_one_of_neg₀ hℓ1
    push_cast
    linarith

end Symbol

end Langlands.Global.CyclotomicSymbol

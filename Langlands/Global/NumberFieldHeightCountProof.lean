import Langlands.Global.NumberFieldHeightCountStatement
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Data.Int.Interval

/-! # Polynomial Northcott bound over a number field -/

noncomputable section

namespace Langlands.Global

open Height Module NumberField

private theorem infinitePlace_le_mulHeight₁ {K : Type*} [Field K] [NumberField K]
    (w : InfinitePlace K) (x : K) : w x ≤ mulHeight₁ x := by
  rw [NumberField.mulHeight₁_eq]
  have hfactor (v : InfinitePlace K) : 1 ≤ max (v x) 1 ^ v.mult :=
    one_le_pow₀ (le_max_right _ _)
  calc
    w x ≤ max (w x) 1 := le_max_left _ _
    _ ≤ max (w x) 1 ^ w.mult := le_self_pow₀ (le_max_right _ _) w.mult_ne_zero
    _ ≤ ∏ v : InfinitePlace K, max (v x) 1 ^ v.mult := by
      simpa only [max_eq_left (hfactor _)] using
        Finset.le_prod_max_one (Finset.mem_univ w) (fun v => max (v x) 1 ^ v.mult)
    _ ≤ _ := le_mul_of_one_le_right
      (Finset.prod_nonneg fun v _ => zero_le_one.trans (hfactor v))
      (one_le_finprod fun _ => le_max_right _ _)

open scoped Classical in
private theorem norm_mixedEmbedding_le_mulHeight₁ {K : Type*} [Field K] [NumberField K]
    (x : K) : ‖mixedEmbedding K x‖ ≤ mulHeight₁ x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  apply Finset.sup'_le
  intro w _
  rw [mixedEmbedding.normAtPlace_apply]
  exact infinitePlace_le_mulHeight₁ w x

universe u

/-- A polynomial upper bound for the number of elements of bounded height. -/
theorem numberFieldMulHeightCount : NumberFieldMulHeightCountStatement.{u} := by
  intro K _ _
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  let coordinates : mixedEmbedding.mixedSpace K →L[ℝ] (ι → ℝ) :=
    (mixedEmbedding.latticeBasis K).equivFun.toLinearMap.toContinuousLinearMap
  let A : ℝ := max 1 ‖coordinates‖
  have hA : 1 ≤ A := le_max_left _ _
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  let d := Fintype.card ι
  refine ⟨(2 * A + 1) ^ d, 2 * d + 1, ?_⟩
  intro B hB
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  let S : Set K := {x | mulHeight₁ x ≤ B}
  let : Fintype S := (NumberField.finite_setOfPred_mulHeight₁_le K B).fintype
  let denominator (x : S) : ℕ := Algebra.natDenominator (x : K)
  let numerator (x : S) : 𝓞 K :=
    ⟨(denominator x : K) * (x : K), by
      rw [mem_integralClosure_iff, ← nsmul_eq_mul]
      exact Algebra.isIntegral_natDenominator_smul (x : K)⟩
  have denominator_ne_zero (x : S) : denominator x ≠ 0 :=
    IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr
      (IsAlgebraic.of_finite ℚ (x : K)))
  have denominator_le (x : S) : (denominator x : ℝ) ≤ B :=
    (NumberField.natDenominator_le_mulHeight₁ (x : K)).trans x.property
  have hnum (x : S) : ‖mixedEmbedding K (numerator x : K)‖ ≤ B ^ 2 := by
    change ‖mixedEmbedding K ((denominator x : K) * (x : K))‖ ≤ B ^ 2
    rw [← nsmul_eq_mul, map_nsmul]
    calc
      _ ≤ (denominator x : ℝ) * ‖mixedEmbedding K (x : K)‖ := norm_nsmul_le
      _ ≤ B * B := mul_le_mul (denominator_le x)
        ((norm_mixedEmbedding_le_mulHeight₁ (x : K)).trans x.property) (norm_nonneg _) hB₀
      _ = B ^ 2 := (pow_two B).symm
  let coeff (x : S) (i : ι) : ℤ := (RingOfIntegers.basis K).repr (numerator x) i
  have coeff_eq (x : S) (i : ι) : coordinates (mixedEmbedding K (numerator x : K)) i =
      (coeff x i : ℝ) := by
    change (mixedEmbedding.latticeBasis K).equivFun (mixedEmbedding K (numerator x : K)) i = _
    rw [Basis.equivFun_apply, mixedEmbedding.latticeBasis_repr_apply,
      RingOfIntegers.coe_eq_algebraMap, NumberField.integralBasis_repr_apply]
    simp [coeff]
  have coeff_bound (x : S) (i : ι) : |(coeff x i : ℝ)| ≤ A * B ^ 2 := by
    rw [← coeff_eq x i, ← Real.norm_eq_abs]
    calc
      _ ≤ ‖coordinates (mixedEmbedding K (numerator x : K))‖ := norm_le_pi_norm _ i
      _ ≤ ‖coordinates‖ * ‖mixedEmbedding K (numerator x : K)‖ := coordinates.le_opNorm _
      _ ≤ _ := mul_le_mul (le_max_right _ _) (hnum x) (norm_nonneg _) hA₀
  let L : ℤ := ⌊A * B ^ 2⌋
  let interval := Finset.Icc (-L) L
  let encode (x : S) : Fin ⌊B⌋₊ × (ι → ↥interval) :=
    (⟨denominator x - 1, by
        have h := Nat.le_floor (denominator_le x)
        have hn := denominator_ne_zero x
        omega⟩,
      fun i => ⟨coeff x i, by
        have h := abs_le.mp (coeff_bound x i)
        have hlo : -(coeff x i) ≤ L := Int.le_floor.mpr (by push_cast; linarith [h.1])
        have hhi : coeff x i ≤ L := Int.le_floor.mpr h.2
        exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩⟩)
  have hencode : Function.Injective encode := by
    intro x y h
    have hd₀ : denominator x - 1 = denominator y - 1 := congrArg (fun p => p.1.val) h
    have hx := denominator_ne_zero x
    have hy := denominator_ne_zero y
    have hd : denominator x = denominator y := by omega
    have ha : numerator x = numerator y := by
      apply (RingOfIntegers.basis K).repr.injective
      ext i
      exact congrArg (fun p => (p.2 i).val) h
    have heq : (denominator x : K) * (x : K) = (denominator y : K) * (y : K) :=
      congrArg (fun a : 𝓞 K => (a : K)) ha
    rw [← hd] at heq
    exact Subtype.ext (mul_left_cancel₀ (by exact_mod_cast hx) heq)
  have hcard : S.ncard ≤ ⌊B⌋₊ * interval.card ^ d := by
    simpa [d] using Fintype.card_le_of_injective encode hencode
  have hL : 0 ≤ L := Int.floor_nonneg.mpr (by positivity)
  have hI : (interval.card : ℤ) = L + 1 - (-L) :=
    Int.card_Icc_of_le (-L) L (by omega)
  have hcardI : (interval.card : ℝ) ≤ (2 * A + 1) * B ^ 2 := by
    have hI' : (interval.card : ℝ) = (L : ℝ) + 1 - (-(L : ℝ)) := by exact_mod_cast hI
    have hL' : (L : ℝ) ≤ A * B ^ 2 := Int.floor_le _
    linarith [one_le_pow₀ hB (n := 2)]
  change (S.ncard : ℝ) ≤ _
  calc
    _ ≤ (⌊B⌋₊ : ℝ) * (interval.card : ℝ) ^ d := by exact_mod_cast hcard
    _ ≤ B * ((2 * A + 1) * B ^ 2) ^ d :=
      mul_le_mul (Nat.floor_le hB₀) (pow_le_pow_left₀ (Nat.cast_nonneg _) hcardI _)
        (by positivity) hB₀
    _ = (2 * A + 1) ^ d * B ^ (2 * d + 1) := by
      rw [mul_pow, ← pow_mul, pow_succ]
      ring

end Langlands.Global

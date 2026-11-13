import Langlands.Representation.RankinSelberg.RootSpectralWeightProof
import Langlands.AllField.Representation.RankinSelberg.RootCoordinateProof
import Langlands.AllField.Representation.RankinSelberg.RootSpectralWeightStatement
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding RootCoordinateChangeStatement RootSpectralWeightStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply rootCoordinateChange rootSpectralWeight
open Langlands.AllField.RankinSelberg

open scoped BigOperators

universe uF

private theorem prod_cpow_nonneg {ι : Type*} (I : Finset ι) (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) (s : ℂ) :
    ((∏ i ∈ I, r i : ℝ) : ℂ) ^ s = ∏ i ∈ I, (r i : ℂ) ^ s := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hr i) (Finset.prod_nonneg fun j _ => hr j), ih]

private theorem pow_cpow_nonneg (r : ℝ) (hr : 0 ≤ r) (m : ℕ) (s : ℂ) :
    ((r ^ m : ℝ) : ℂ) ^ s = (r : ℂ) ^ ((m : ℂ) * s) := by
  rw [Complex.ofReal_pow]
  symm
  apply Complex.cpow_nat_mul'
  · simpa only [Complex.arg_ofReal_of_nonneg hr, mul_zero] using neg_lt_zero.mpr Real.pi_pos
  · simpa only [Complex.arg_ofReal_of_nonneg hr, mul_zero] using Real.pi_pos.le

/-- The determinant spectral factor has the expected positive root exponents. -/
theorem rootSpectralWeight 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    RootSpectralWeightStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  constructor
  · intro k
    have hv := Conductor.valuation_det_of_mem_integralSubgroup k.property
    have hx : Matrix.det k.val.val ≠ 0 := by
      intro hx
      rw [hx, map_zero] at hv
      exact zero_ne_one hv
    have hd : T.discreteValuation (Matrix.det k.val.val) = 1 := by
      change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
        (ValuativeRel.valuation F (Matrix.det k.val.val)) = 1
      rw [hv, map_one]
    rw [T.normalizedAbs_of_ne_zero hx]
    simp [Langlands.LocalFieldData.ord, hd]
  · intro a k hk s
    let d : (Fin (n + 1) → Fˣ) → (Fin (n + 1) → Fˣ) :=
      fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
    have hdet : Matrix.det (GeneralLinear.Iwasawa.diagonalUnits (d a)).val =
        ∏ i, (a i : F) ^ (i.val + 1) :=
      ((rootCoordinateChange F T n).2.2.2.2.2.2 a).2.2.1
    have hnorm :
        normalizedAbsoluteValue T
          (Matrix.det (GeneralLinear.Iwasawa.diagonalUnits (d a) * k).val) =
          ∏ i, T.normalizedAbs (a i : F) ^ (i.val + 1) := by
      change normalizedAbsoluteValue T
        (Matrix.det ((GeneralLinear.Iwasawa.diagonalUnits (d a)).val * k.val)) = _
      rw [Matrix.det_mul, map_mul,
        show normalizedAbsoluteValue T (Matrix.det k.val) = 1 from hk,
        mul_one, hdet]
      simp only [map_prod, map_pow, normalizedAbsoluteValue_apply]
    have hweight :
        determinantWeight (normalizedAbsoluteValue T)
          (GeneralLinear.Iwasawa.diagonalUnits (d a) * k) s =
          ∏ i, (T.normalizedAbs (a i : F) : ℂ) ^ ((i.val + 1 : ℂ) * s) := by
      unfold determinantWeight
      rw [hnorm, prod_cpow_nonneg _ _ (fun i => pow_nonneg (T.normalizedAbs_nonneg _) _)]
      apply Finset.prod_congr rfl
      intro i _
      simpa only [Nat.cast_add, Nat.cast_one] using
        pow_cpow_nonneg (T.normalizedAbs (a i : F))
          (T.normalizedAbs_nonneg _) (i.val + 1) s
    refine ⟨hweight, ?_⟩
    change ‖determinantWeight (normalizedAbsoluteValue T)
      (GeneralLinear.Iwasawa.diagonalUnits (d a) * k) s‖ = _
    rw [hweight, norm_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (T.normalizedAbs_pos (a i).ne_zero)]
    simp

end Langlands.AllField.RankinSelberg

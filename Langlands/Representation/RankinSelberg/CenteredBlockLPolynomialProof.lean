import Langlands.Representation.RankinSelberg.CenteredBlockLPolynomialStatement
import Langlands.Representation.RankinSelberg.GroupedLFactorReduction
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.Parabolic.InverseTransposeProductProof

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial GeneralLinear Whittaker HarmonicAnalysis SegmentGammaTelescoping

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

theorem centeredHalfShiftUnit_zpow (k : ℤ) :
    centeredHalfShiftUnit F ^ k =
      spectralShiftUnit F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.residueCardinality_gt_one ((k : ℂ) / 2) := by
  apply Units.ext
  simp only [centeredHalfShiftUnit, Units.val_zpow_eq_zpow_val,
    coe_spectralShiftUnit, spectralPoint]
  rw [← Complex.cpow_int_mul]
  congr 1
  ring

theorem centeredHalfShiftUnit_sq :
    centeredHalfShiftUnit F ^ (2 : ℕ) = LocalFactor.residueReflection F := by
  apply Units.ext
  simp only [centeredHalfShiftUnit, Units.val_pow_eq_pow_val,
    coe_spectralShiftUnit, spectralPoint, LocalFactor.coe_residueReflection]
  rw [← Complex.cpow_nat_mul]
  norm_num [Complex.cpow_neg_one]

theorem norm_centeredHalfShiftUnit_le_one : ‖(centeredHalfShiftUnit F : ℂ)‖ ≤ 1 := by
  simp only [centeredHalfShiftUnit, coe_spectralShiftUnit, spectralPoint]
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos F.canonicalTopologicalData.residueCardinality_real_pos]
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast Nat.le_of_lt F.canonicalTopologicalData.residueCardinality_gt_one
  · norm_num

theorem polynomialRescale_linearFactor (c a : ℂˣ) :
    polynomialRescale c (linearFactor a) = linearFactor (a * c) := by
  simp only [polynomialRescale_apply, linearFactor, sub_comp, one_comp,
    mul_comp, C_comp, X_comp, Units.val_mul, map_mul, mul_assoc]

theorem polynomialRescale_parameterProduct (c : ℂˣ) (A : Finset ℂˣ) :
    polynomialRescale c (∏ a ∈ A, linearFactor a) =
      ∏ a ∈ A, linearFactor (a * c) := by
  simp only [map_prod, polynomialRescale_linearFactor]

private theorem realTwistPolynomial_twice (s z : ℝ) (P : ℂ[X]) :
    realTwistPolynomial F z (realTwistPolynomial F s P) =
      polynomialRescale
        (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
          F.canonicalTopologicalData.residueCardinality_gt_one ((s : ℂ) + (z : ℂ))) P := by
  have hq : (F.canonicalTopologicalData.residueCardinality : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by
      have := F.canonicalTopologicalData.residueCardinality_gt_one
      omega)
  simp only [realTwistPolynomial, coe_compRingHom_apply, polynomialRescale_apply,
    coe_spectralShiftUnit, spectralPoint, comp_assoc, mul_comp, C_comp, X_comp,
    ← mul_assoc, ← C_mul, neg_add, Complex.cpow_add _ _ hq]

theorem inverseTransposePullback_realPowerTwist {a : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V) (s : ℝ) :
    inverseTransposePullback
        (realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) s π) =
      realPowerTwist (F.canonicalTopologicalData.determinantNorm (a + 1)) (-s)
        (inverseTransposePullback π) := by
  exact Parabolic.inverseTransposeDeterminantTwist
    F.canonicalTopologicalData (a + 1) V π s

theorem centeredBlockLPolynomial : CenteredBlockLPolynomialStatement.{uF, uV, uW} := by
  intro p _ F ψ ν a b m n V _ _ W _ _ π σ P PD hP hPD i j
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have he :
      (((m : ℝ) / 2 - (i : ℕ) : ℝ) : ℂ) +
          (((n : ℝ) / 2 - (j : ℕ) : ℝ) : ℂ) =
        (blockExponent m n i.val j.val : ℂ) / 2 := by
    simp only [blockExponent]
    push_cast
    ring
  constructor
  · have h := IsPadicRankLPolynomial.twist_real F ψ ν (n := a + 1) (t := b + 1) hP
      ((m : ℝ) / 2 - (i : ℕ)) ((n : ℝ) / 2 - (j : ℕ))
    rw [realTwistPolynomial_twice, he, ← centeredHalfShiftUnit_zpow] at h
    exact h
  · have h := IsPadicRankLPolynomial.twist_real F (ψ.scale (-1))
      (DominantRankTransport.negatedSelfDualHaar F ψ ν)
      (n := a + 1) (t := b + 1) hPD
      (-((m : ℝ) / 2 - (i : ℕ))) (-((n : ℝ) / 2 - (j : ℕ)))
    have hed :
        ((-((m : ℝ) / 2 - (i : ℕ)) : ℝ) : ℂ) +
            ((-((n : ℝ) / 2 - (j : ℕ)) : ℝ) : ℂ) =
          ((-blockExponent m n i.val j.val : ℤ) : ℂ) / 2 := by
      simp only [blockExponent]
      push_cast
      ring
    rw [realTwistPolynomial_twice, hed, ← centeredHalfShiftUnit_zpow] at h
    simpa only [centeredSegmentBlocks, inverseTransposePullback_realPowerTwist,
      DominantRankTransport.negatedSelfDualHaar_val] using
      (isPadicRankLPolynomial_succ (r := a) (k := b)).mp h

end Langlands.RankinSelberg

import Langlands.Representation.RankinSelberg.OneVariableMellinStatement
import Langlands.Representation.RankinSelberg.FiniteFunctionShellSeriesProof
import Langlands.Representation.RankinSelberg.EpsilonFactor
import Langlands.Analysis.EventuallyRecurrentLaurentSeriesProof
import Langlands.LocalField.Normalization.Proof
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted one-variable Mellin integrals

This module proves the full one-variable Mellin statement by combining
actual shell generating integrals and eventual-recurrence Laurent rationality.
The elementary spectral helpers adapt Worker 235's private proofs in
RamifiedFiniteFunctionMellinProof; see the paired Markdown for attribution.
-/

noncomputable section
namespace Langlands.RankinSelberg
open MeasureTheory HarmonicAnalysis
universe uF

/-- The weighted normalized absolute value is an integer power of the spectral
point. Positivity of `q` fixes the logarithm branch. -/
private theorem mellin_natCast_zpow_cpow_eq (q : ℕ) (hq : 0 < q) (k : ℤ) (m : ℕ) (s : ℂ) :
    ((((q : ℝ) ^ (-k) : ℝ)) : ℂ) ^ ((m : ℂ) * s) = (spectralPoint q s ^ m) ^ k := by
  have harg : Complex.arg (q : ℂ) = 0 := by
    simpa only [Complex.ofReal_natCast] using
      Complex.arg_ofReal_of_nonneg (show 0 ≤ (q : ℝ) by positivity)
  rw [Complex.ofReal_zpow, Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [harg, Real.pi_pos])
      (by simpa only [harg, mul_zero] using Real.pi_pos.le),
    spectralPoint, ← zpow_natCast, ← zpow_mul, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

/-- Positive powers of the spectral point are small on a right half-plane. -/
private theorem mellin_exists_re_threshold {q : ℕ} (hq : 1 < q) {m : ℕ} (hm : 0 < m) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ c : ℝ, ∀ s : ℂ, c < s.re → ‖spectralPoint q s ^ m‖ < ρ := by
  set ρ1 := min ρ 1 with hρ1_def
  have hρ1 : 0 < ρ1 := lt_min hρ one_pos
  have hq0 : 0 < q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine ⟨-Real.log ρ1 / Real.log q, fun s hs => ?_⟩
  have hnorm : ‖spectralPoint q s‖ = (q : ℝ) ^ (-s.re) := by
    rw [spectralPoint, Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re]
  have ht : (q : ℝ) ^ (-s.re) < ρ1 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hq0), ← Real.lt_log_iff_exp_lt hρ1]
    rw [div_lt_iff₀ hlogq] at hs
    linarith
  have ht0 : 0 ≤ (q : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  rw [norm_pow, hnorm]
  calc ((q : ℝ) ^ (-s.re)) ^ m ≤ (q : ℝ) ^ (-s.re) :=
        pow_le_of_le_one ht0 (ht.le.trans (min_le_right _ _)) hm.ne'
    _ < ρ1 := ht
    _ ≤ ρ := min_le_left _ _

private theorem mellin_normalizedAbs_cpow {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData)
    (a : F.Carrierˣ) (m : ℕ) (s : ℂ) :
    (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s) =
      (spectralPoint T.residueCardinality s ^ m) ^ T.ord (a : F.Carrier) := by
  rw [T.normalizedAbs_of_ne_zero a.ne_zero,
    mellin_natCast_zpow_cpow_eq T.residueCardinality (by
      have := T.residueCardinality_gt_one
      omega)]

private theorem mellin_exists_joint_threshold {q : ℕ} (hq : 1 < q)
    {m : ℕ} (hm : 0 < m) {B ρ : ℝ} (hB : 1 ≤ B) (hρ : 0 < ρ) :
    ∃ c : ℝ, ∀ s : ℂ, c < s.re →
      B * ‖spectralPoint q s ^ m‖ < 1 ∧ ‖spectralPoint q s ^ m‖ < ρ := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨c, hc⟩ := mellin_exists_re_threshold hq hm
    (lt_min (one_div_pos.mpr hBpos) hρ)
  refine ⟨c, fun s hs => ?_⟩
  have hsmall := hc s hs
  refine ⟨?_, hsmall.trans_le (min_le_right _ _)⟩
  have hsmallB : ‖spectralPoint q s ^ m‖ < 1 / B :=
    hsmall.trans_le (min_le_left _ _)
  nlinarith [(lt_div_iff₀ hBpos).mp hsmallB]

/-- Actual weighted Mellin convergence, rational continuation and a single
Laurent denominator for all Schwartz--Bruhat tests and all continuations. -/
theorem oneVariableMellin : OneVariableMellinStatement.{uF} := by
  intro p hp F T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace F.Carrierˣ := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  intro m hm η hη hηfin dA integrand mellin rationalValues
  obtain ⟨π, E, B, _hπ, hB, hShellTests⟩ := finiteFunctionShellSeries p hp F T η hη hηfin
  obtain ⟨_hQ, ρ, hρ, hWeights⟩ := Langlands.Analysis.eventuallyRecurrentLaurentSeriesStatement_proof E
  obtain ⟨hD, hRepresent⟩ := hWeights m hm
  let Q : Polynomial ℂ :=
    1 - ∑ i : Fin E.order,
      Polynomial.C (E.coeffs i) * Polynomial.X ^ (E.order - i.val)
  let D : LaurentPolynomial ℂ := (Q.comp (Polynomial.X ^ m)).toLaurent
  change D ≠ 0 at hD
  obtain ⟨c0, hc0⟩ :=
    mellin_exists_joint_threshold T.residueCardinality_gt_one hm hB hρ
  have htest (Φ : SchwartzBruhat F.Carrier) :
      (∀ s : ℂ, c0 < s.re → Integrable (integrand Φ s) dA) ∧
        ∃ (R : RationalFunctions) (P : LaurentCoefficients),
          HasRationalContinuation T.residueCardinality (mellin Φ) R ∧
            laurentToRatFunc P = laurentToRatFunc D * R := by
    obtain ⟨L, N, hLN, hlow, hrec, hIntegral⟩ := hShellTests Φ
    obtain ⟨R, P, hclear, hEval⟩ := hRepresent _ L N hLN hlow hrec
    have hz (s : ℂ) : spectralPoint T.residueCardinality s ≠ 0 :=
      spectralPoint_ne_zero T.residueCardinality_gt_one s
    refine ⟨?_, R, P, ⟨c0, ?_⟩, hclear⟩
    · intro s hs
      change Integrable (fun a : F.Carrierˣ =>
        Φ (a : F.Carrier) * η a *
          (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s)) _
      simp_rw [mellin_normalizedAbs_cpow T]
      exact (hIntegral _ (pow_ne_zero m (hz s)) (hc0 s hs).1).1
    · intro s hs
      have hI := hIntegral _ (pow_ne_zero m (hz s)) (hc0 s hs).1
      have hR := hEval _ (hz s) (hc0 s hs).2
      refine ⟨hR.2.1, ?_⟩
      change (∫ a : F.Carrierˣ,
        Φ (a : F.Carrier) * η a *
          (T.normalizedAbs (a : F.Carrier) : ℂ) ^ ((m : ℂ) * s) ∂dA) = _
      simp_rw [mellin_normalizedAbs_cpow T]
      exact hI.2.2.trans hR.2.2
  refine ⟨fun Φ => ⟨c0, (htest Φ).1⟩, ?_, D, hD, ?_⟩
  · intro Φ
    obtain ⟨R, _P, hR, _hP⟩ := (htest Φ).2
    exact ⟨R, hR⟩
  · intro R hR
    obtain ⟨Φ, hΦR⟩ := hR
    obtain ⟨S, P, hS, hP⟩ := (htest Φ).2
    refine ⟨P, ?_⟩
    rw [hΦR.unique T.residueCardinality_gt_one hS]
    exact hP

end Langlands.RankinSelberg

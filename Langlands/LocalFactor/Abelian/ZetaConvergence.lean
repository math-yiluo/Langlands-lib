import Langlands.LocalFactor.Abelian.ZetaShells
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open MeasureTheory Filter Topology
open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "TestFunction" => @HarmonicAnalysis.SchwartzBruhat F.Carrier T.topology

@[simp] theorem characterExtension_unit (χ : Character) (v : F.Carrierˣ) :
    characterExtension T χ (v : F.Carrier) = (χ v : ℂ) := by
  simp [characterExtension]

/-- Multiplication on the nonzero locus respects the extended character. -/
theorem characterExtension_mul_unit (χ : Character) (a : F.Carrierˣ)
    (x : F.Carrier) :
    characterExtension T χ ((a : F.Carrier) * x) =
      (χ a : ℂ) * characterExtension T χ x := by
  classical
  by_cases hx : x = 0
  · simp [hx, characterExtension]
  · have he : (a : F.Carrier) * x = ((a * Units.mk0 x hx : F.Carrierˣ) : F.Carrier) := rfl
    rw [he, characterExtension_unit, map_mul, Units.val_mul]
    simp [characterExtension, hx]

/-- The logarithm of the normalized absolute value is constant on an order shell. -/
theorem log_normalizedAbs_orderShell (k : ℤ) {x : F.Carrier}
    (hx : x ∈ orderShell T k) :
    Real.log (T.normalizedAbs x) =
      -(k : ℝ) * Real.log (T.residueCardinality : ℝ) := by
  rw [T.normalizedAbs_of_ne_zero hx.1, hx.2, Real.log_zpow]
  simp

/-- The real Haar scaling factor is the corresponding complex exponential. -/
theorem ofReal_residue_zpow (k : ℤ) :
    (((T.residueCardinality : ℝ) ^ k : ℝ) : ℂ) =
      Complex.exp ((k : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
  rw [Complex.exp_int_mul, ← Complex.ofReal_exp,
    Real.exp_log (by exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one))]
  norm_cast

/-- Cancellation of additive Haar scaling against the shift by one in the integrand. -/
theorem scaled_zetaIntegrand_on_units (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (f : F.Carrier → ℂ)
    (s : ℂ) (k : ℤ) {x : F.Carrier} (hx : x ∈ integralUnits T) :
    (T.residueCardinality : ℝ) ^ (-k) •
        zetaIntegrand T f χ s (((π ^ k : F.Carrierˣ) : F.Carrier) * x) =
      ((χ π : ℂ) * spectralVariable T s) ^ k *
        (f (((π ^ k : F.Carrierˣ) : F.Carrier) * x) * characterExtension T χ x) := by
  classical
  have hm := (mul_uniformizer_mem_orderShell_iff T π hπ k x).mpr hx
  rw [zetaIntegrand, ite_eq_right hm.1, characterExtension_mul_unit,
    log_normalizedAbs_orderShell T k hm, map_zpow, Units.val_zpow_eq_zpow_val]
  rw [Complex.real_smul, ofReal_residue_zpow]
  simp only [Int.cast_neg, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_intCast]
  rw [mul_zpow, spectralVariable, ← Complex.exp_int_mul]
  rw [show (-(k : ℂ)) * (Real.log (T.residueCardinality : ℝ) : ℂ) +
        (s - 1) * (-(k : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) =
      (k : ℂ) * (-s * (Real.log (T.residueCardinality : ℝ) : ℂ)) by ring
    |>.symm, Complex.exp_add]
  simp only [Units.val_zpow_eq_zpow_val]
  ring

/-- Each actual shell integral is a monomial times an integral over integral units. -/
theorem setIntegral_zeta_orderShell (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (μ : LocalHaar)
    (f : F.Carrier → ℂ) (s : ℂ) (k : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    (∫ x in orderShell T k, zetaIntegrand T f χ s x ∂μ.measure) =
      ((χ π : ℂ) * spectralVariable T s) ^ k *
        ∫ x in integralUnits T,
          f (((π ^ k : F.Carrierˣ) : F.Carrier) * x) * characterExtension T χ x ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  rw [setIntegral_orderShell T μ π hπ, ← integral_smul, ← integral_const_mul]
  exact setIntegral_congr_fun (orderShell_compact_measurable T 0).2
    (fun x hx => scaled_zetaIntegrand_on_units T π hπ χ f s k hx)

/-- The explicit convergence predicate is the geometric series norm condition. -/
theorem convergesAt_iff_norm_lt_one (π : F.Carrierˣ) (χ : Character) (s : ℂ) :
    ConvergesAt T π χ s ↔ ‖(χ π : ℂ) * spectralVariable T s‖ < 1 := by
  simp only [ConvergesAt, norm_mul, spectralVariable, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The raw integrand is continuous on every compact shell. -/
theorem zetaIntegrand_integrableOn_orderShell (χ : Character) (μ : LocalHaar)
    (f : TestFunction) (s : ℂ) (k : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    IntegrableOn (zetaIntegrand T f χ s) (orderShell T k) μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have hc : ContinuousOn (fun x => f x * characterExtension T χ x *
      Complex.exp ((s - 1) * (-(k : ℝ) * Real.log (T.residueCardinality : ℝ) : ℝ))) 
      (orderShell T k) :=
    (f.continuous.continuousOn.mul
      ((HarmonicAnalysis.Quasicharacter.continuousOn_extendZero χ).mono
        (fun _x hx => hx.1))).mul_const _
  apply (hc.integrableOn_compact' (orderShell_compact_measurable T k).1
    (orderShell_compact_measurable T k).2).congr_fun
  · intro x hx
    simp only [zetaIntegrand, ite_eq_right hx.1, log_normalizedAbs_orderShell T k hx]
  · exact (orderShell_compact_measurable T k).2

/-- On the integral units the extended quasicharacter has norm one. -/
theorem norm_characterExtension_on_units (χ : Character) {x : F.Carrier}
    (hx : x ∈ integralUnits T) : ‖characterExtension T χ x‖ = 1 := by
  classical
  rw [characterExtension, dite_eq_right hx.1]
  exact quasicharacter_norm_units T χ (Units.mk0 x hx.1)
    (by simpa [unitLevel] using hx.2)

/-- The same shell formula for absolute integrals. -/
theorem setIntegral_norm_zeta_orderShell (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (μ : LocalHaar)
    (f : F.Carrier → ℂ) (s : ℂ) (k : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    (∫ x in orderShell T k, ‖zetaIntegrand T f χ s x‖ ∂μ.measure) =
      ‖((χ π : ℂ) * spectralVariable T s) ^ k‖ *
        ∫ x in integralUnits T, ‖f (((π ^ k : F.Carrierˣ) : F.Carrier) * x)‖ ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  rw [setIntegral_orderShell T μ π hπ, ← integral_smul, ← integral_const_mul]
  apply setIntegral_congr_fun (orderShell_compact_measurable T 0).2
  intro x hx
  have h := congrArg norm (scaled_zetaIntegrand_on_units T π hπ χ f s k hx)
  have hq : 0 < (T.residueCardinality : ℝ) ^ (-k) :=
    zpow_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)) _
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hq, norm_mul,
    norm_characterExtension_on_units T χ hx, mul_one, smul_eq_mul] using h

/-- A uniform test-function bound gives a geometric bound on the absolute shell integrals. -/
theorem setIntegral_norm_zeta_orderShell_le (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (μ : LocalHaar)
    (f : F.Carrier → ℂ) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) (s : ℂ) (k : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    (∫ x in orderShell T k, ‖zetaIntegrand T f χ s x‖ ∂μ.measure) ≤
      ‖((χ π : ℂ) * spectralVariable T s) ^ k‖ *
        (C * (μ.measure (integralUnits T)).toReal) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  rw [setIntegral_norm_zeta_orderShell T π hπ]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hU : μ.measure (integralUnits T) < ⊤ :=
    (orderShell_compact_measurable T 0).1.measure_lt_top
  have hb := norm_setIntegral_le_of_norm_le_const (μ := μ.measure)
    (f := fun x => ‖f (((π ^ k : F.Carrierˣ) : F.Carrier) * x)‖) hU
    (fun x (_hx : x ∈ integralUnits T) => by
      simpa only [Real.norm_eq_abs, abs_norm] using hC (((π ^ k : F.Carrierˣ) : F.Carrier) * x))
  have hn : 0 ≤ ∫ x in integralUnits T,
      ‖f (((π ^ k : F.Carrierˣ) : F.Carrier) * x)‖ ∂μ.measure :=
    integral_nonneg (fun _ => norm_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn,
    measureReal_def] using hb

/-- The support of the integrand is covered by a sequence of shells starting at a lower cutoff. -/
theorem support_zetaIntegrand_subset_shells (χ : Character) (f : F.Carrier → ℂ)
    (s : ℂ) (L : ℤ)
    (hL : ∀ a : F.Carrierˣ, T.ord (a : F.Carrier) < L → f (a : F.Carrier) = 0) :
    Function.support (zetaIntegrand T f χ s) ⊆ ⋃ n : ℕ, orderShell T (L + n) := by
  classical
  intro x hx
  have hx0 : x ≠ 0 := by
    intro he
    exact hx (by simp [zetaIntegrand, he])
  have hord : L ≤ T.ord x := by
    by_contra hn
    have hz := hL (Units.mk0 x hx0) (by simpa using lt_of_not_ge hn)
    change f x = 0 at hz
    exact hx (by simp [zetaIntegrand, hz])
  refine Set.mem_iUnion.mpr ⟨(T.ord x - L).toNat, hx0, ?_⟩
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- Actual absolute convergence of every Schwartz--Bruhat zeta integral in the stated half-plane. -/
theorem zeta_integrable (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ : Character) (μ : LocalHaar) (f : TestFunction) (s : ℂ)
    (hs : ConvergesAt T π χ s) :
    letI := T.topology
    letI := borel F.Carrier
    Integrable (zetaIntegrand T f χ s) μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  obtain ⟨L, N, C, _hLN, _hC, hbound, hL, _hN⟩ :=
    HarmonicAnalysis.schwartzBruhatValuationBounds p F T f
  let r := (χ π : ℂ) * spectralVariable T s
  have hr : ‖r‖ < 1 := (convergesAt_iff_norm_lt_one T π χ s).mp hs
  have hr0 : r ≠ 0 := mul_ne_zero (χ π).ne_zero (spectralVariable_ne_zero T s)
  have hsum : Summable (fun n : ℕ =>
      ‖r ^ (L + n)‖ * (C * (μ.measure (integralUnits T)).toReal)) := by
    have hg := (summable_geometric_of_norm_lt_one hr).norm.mul_left
      (‖r ^ L‖ * (C * (μ.measure (integralUnits T)).toReal))
    simpa only [zpow_add₀ hr0,
      zpow_natCast, norm_mul, norm_pow, mul_assoc, mul_left_comm, mul_comm] using hg
  have hsum' : Summable (fun n : ℕ =>
      ∫ x in orderShell T (L + n), ‖zetaIntegrand T f χ s x‖ ∂μ.measure) :=
    hsum.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun n => setIntegral_norm_zeta_orderShell_le T π hπ χ μ f C hbound s (L + n))
  have hi := integrableOn_iUnion_of_summable_integral_norm
    (fun n : ℕ => zetaIntegrand_integrableOn_orderShell T χ μ f s (L + n)) hsum'
  exact (integrableOn_iff_integrable_of_support_subset
    (support_zetaIntegrand_subset_shells T χ f s L hL)).mp hi

end Langlands.LocalFactor.PadicAbelian

import Langlands.LocalFactor.PadicAbelianStatement
import Langlands.LocalField.Normalization.Proof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.LocalFactor.Abelian.Scaling
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Elementary laws of the concrete Gauss epsilon expression

Spectral dependence, uniformizer and shell independence, Haar, character and
unramified-twist laws for `PadicAbelian.epsilonAt`, at explicit conductor levels.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

theorem gaussShell_measurableSet (d : ℤ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    MeasurableSet (gaussShell T d) := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  rw [gaussShell_eq_valuationShell]
  exact (T.valuationShell_compact_closed d).2.measurableSet

theorem residueCardinality_pos' : 0 < (T.residueCardinality : ℝ) :=
  by exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)

/-- On the shell of order `-d` the spectral factor of the Gauss integrand is
`q^(-d s)` times its value at `s = 0`. -/
theorem gaussIntegrand_on_shell_spectral (χ : Character) (ψ : AddChar F.Carrier Circle)
    (d : ℤ) (s : ℂ) {x : F.Carrier} (hx : x ∈ gaussShell T d) :
    gaussIntegrand T χ ψ s x = gaussIntegrand T χ ψ 0 x *
      Complex.exp (-(d : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
  rw [gaussIntegrand, gaussIntegrand, normalizedAbs_on_gaussShell T d hx, Real.log_zpow]
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one, Complex.ofReal_mul,
    Complex.ofReal_intCast]
  rw [mul_right_comm _ _ (ψ x : ℂ)]
  congr 2
  ring

/-- Spectral dependence of the epsilon expression at arbitrary explicit levels. -/
theorem epsilonAt_eq_zero_mul (π : F.Carrierˣ) (χ : Character) (ψ : AddChar F.Carrier Circle)
    (μ : BorelMeasure T) (a : ℕ) (n : ℤ) (s : ℂ) :
    epsilonAt T π χ ψ μ a n s = epsilonAt T π χ ψ μ a n 0 *
      Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  unfold epsilonAt
  split_ifs with ha
  · subst ha
    simp only [Nat.cast_zero, add_zero, sub_zero, mul_one]
    have he : Complex.exp ((n : ℂ) * (1 - s) * (Real.log (T.residueCardinality : ℝ) : ℂ)) =
        Complex.exp ((n : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) *
          Complex.exp (-(n : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [he]; ring
  · rw [← integral_mul_const]
    apply setIntegral_congr_fun (gaussShell_measurableSet T _)
    intro x hx
    exact gaussIntegrand_on_shell_spectral T χ ψ _ s hx

local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

/-- The spectral law centred at `s = 1/2`. -/
theorem epsilonAt_eq_half_mul (π : F.Carrierˣ) (χ : Character) (ψ : AddChar F.Carrier Circle)
    (μ : BorelMeasure T) (a : ℕ) (n : ℤ) (s : ℂ) :
    epsilonAt T π χ ψ μ a n s = epsilonAt T π χ ψ μ a n (1 / 2) *
      Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * (s - 1 / 2) *
        (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
  rw [epsilonAt_eq_zero_mul T π χ ψ μ a n s, epsilonAt_eq_zero_mul T π χ ψ μ a n (1 / 2),
    mul_assoc (epsilonAt T π χ ψ μ a n 0) (Complex.exp _) (Complex.exp _), ← Complex.exp_add]
  congr 2
  ring

theorem epsilonAt_differentiable (π : F.Carrierˣ) (χ : Character)
    (ψ : AddChar F.Carrier Circle) (μ : BorelMeasure T) (a : ℕ) (n : ℤ) :
    Differentiable ℂ (epsilonAt T π χ ψ μ a n) := by
  have h : epsilonAt T π χ ψ μ a n = fun s => epsilonAt T π χ ψ μ a n 0 *
      Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * s *
        (Real.log (T.residueCardinality : ℝ) : ℂ)) :=
    funext (epsilonAt_eq_zero_mul T π χ ψ μ a n)
  rw [h]
  exact (Differentiable.cexp (by fun_prop)).const_mul _

theorem unitLevel_zero_iff (v : F.Carrierˣ) :
    unitLevel T 0 v ↔ T.ord (v : F.Carrier) = 0 := by
  simp [unitLevel]

/-- An unramified quasicharacter is determined by its uniformizer value. -/
theorem chi_eq_zpow_ord (χ : Character) (h0 : ConductorAt T χ 0) {π : F.Carrierˣ}
    (hπ : T.ord (π : F.Carrier) = 1) (b : F.Carrierˣ) :
    (χ b : ℂ) = (χ π : ℂ) ^ T.ord (b : F.Carrier) := by
  set k := T.ord (b : F.Carrier)
  have hu : unitLevel T 0 (b * π ^ (-k)) := by
    rw [unitLevel_zero_iff, Units.val_mul, Units.val_zpow_eq_zpow_val,
      T.ord_mul b.ne_zero (zpow_ne_zero _ π.ne_zero), T.ord_zpow, hπ]
    ring
  have h1 := congrArg (fun u : ℂˣ => (u : ℂ)) (h0.1 _ hu)
  simp only [map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, Units.val_one, zpow_neg] at h1
  exact (mul_inv_eq_one₀ (zpow_ne_zero _ (χ π).ne_zero)).mp h1

theorem lFactorAt_uniformizer_eq (χ : Character) {a : ℕ} (hχ : ConductorAt T χ a)
    {π ρ : F.Carrierˣ} (hπ : T.ord (π : F.Carrier) = 1) (hρ : T.ord (ρ : F.Carrier) = 1)
    (s : ℂ) : lFactorAt T ρ χ a s = lFactorAt T π χ a s := by
  unfold lFactorAt
  split_ifs with ha
  · subst ha
    rw [chi_eq_zpow_ord T χ hχ hπ ρ, hρ, zpow_one]
  · rfl

theorem epsilonAt_uniformizer_eq (χ : Character) (ψ : AddChar F.Carrier Circle)
    (μ : BorelMeasure T) {a : ℕ} (hχ : ConductorAt T χ a) (n : ℤ)
    {π ρ : F.Carrierˣ} (hπ : T.ord (π : F.Carrier) = 1) (hρ : T.ord (ρ : F.Carrier) = 1)
    (s : ℂ) : epsilonAt T ρ χ ψ μ a n s = epsilonAt T π χ ψ μ a n s := by
  unfold epsilonAt
  split_ifs with ha
  · subst ha
    rw [chi_eq_zpow_ord T χ hχ hπ ρ, hρ, zpow_one]
  · rfl

theorem log_normalizedAbs_unit (b : F.Carrierˣ) :
    Real.log (T.normalizedAbs (b : F.Carrier)) =
      -(T.ord (b : F.Carrier) : ℝ) * Real.log (T.residueCardinality : ℝ) := by
  rw [T.normalizedAbs_of_ne_zero b.ne_zero, Real.log_zpow]
  push_cast
  ring

/-- Multiplying the integral units by `c⁻¹` gives the shell of order `-ord c`. -/
theorem image_mul_integralUnits (c : F.Carrierˣ) (d : ℤ) (hc : T.ord (c : F.Carrier) = d) :
    (fun v => ((c⁻¹ : F.Carrierˣ) : F.Carrier) * v) '' integralUnits T = gaussShell T d := by
  ext x
  constructor
  · rintro ⟨v, ⟨hv0, hv⟩, rfl⟩
    refine ⟨mul_ne_zero (c⁻¹).ne_zero hv0, ?_⟩
    rw [T.ord_mul (c⁻¹).ne_zero hv0, hv, Units.val_inv_eq_inv_val, T.ord_inv, hc]
    ring
  · rintro ⟨hx0, hx⟩
    refine ⟨(c : F.Carrier) * x, ⟨mul_ne_zero c.ne_zero hx0, ?_⟩, ?_⟩
    · rw [T.ord_mul c.ne_zero hx0, hx, hc]
      ring
    · simp only [Units.val_inv_eq_inv_val]
      field_simp [c.ne_zero]

/-- The epsilon expression evaluated through any element `c` of order `n + a`. -/
theorem epsilonAt_eq_shell (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1) (χ : Character)
    (ψ : AddChar F.Carrier Circle) (μ : BorelMeasure T) {a : ℕ} (hχ : ConductorAt T χ a)
    (n : ℤ) (c : F.Carrierˣ) (hc : T.ord (c : F.Carrier) = n + a) (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    epsilonAt T π χ ψ μ a n s =
      if a = 0 then (χ c : ℂ) *
        Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (c : F.Carrier)) : ℂ)) *
        (μ (integerRing T)).toReal
      else ∫ x in (fun v => ((c⁻¹ : F.Carrierˣ) : F.Carrier) * v) '' integralUnits T,
        gaussIntegrand T χ ψ s x ∂μ := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  unfold epsilonAt
  split_ifs with ha
  · subst ha
    simp only [Nat.cast_zero, add_zero] at hc
    rw [chi_eq_zpow_ord T χ hχ hπ c, log_normalizedAbs_unit, hc]
    congr 2
    push_cast
    ring_nf
  · rw [image_mul_integralUnits T c _ hc]

theorem epsilonAt_smul_measure (π : F.Carrierˣ) (χ : Character) (ψ : AddChar F.Carrier Circle)
    (μ : BorelMeasure T) (a : ℕ) (n : ℤ) (r : NNReal) (s : ℂ) :
    epsilonAt T π χ ψ ((r : ENNReal) • μ) a n s = (r : ℂ) * epsilonAt T π χ ψ μ a n s := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  unfold epsilonAt
  split_ifs with ha
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
    push_cast
    ring
  · rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul]

theorem characterExtension_unit_mul (χ : Character) (b : F.Carrierˣ) (x : F.Carrier) :
    characterExtension T χ ((b : F.Carrier) * x) = (χ b : ℂ) * characterExtension T χ x := by
  let := T.topology
  exact HarmonicAnalysis.Quasicharacter.extendZero_mul_unit χ b x

theorem gaussIntegrand_mulShift (χ : Character) (ψ : AddChar F.Carrier Circle)
    (b : F.Carrierˣ) (s : ℂ) {x : F.Carrier} (hx : x ≠ 0) :
    gaussIntegrand T χ (ψ.mulShift (b : F.Carrier)) s x =
      (χ b : ℂ) * Complex.exp (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) *
        gaussIntegrand T χ ψ s ((b : F.Carrier) * x) := by
  have hb := T.normalizedAbs_pos b.ne_zero
  have hxp := T.normalizedAbs_pos hx
  simp only [gaussIntegrand, AddChar.mulShift_apply, characterExtension_unit_mul,
    T.normalizedAbs_mul, Real.log_mul hb.ne' hxp.ne', Complex.ofReal_add, mul_inv]
  have hχ := (χ b).ne_zero
  have he : Complex.exp (-s * ((Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ) +
      (Real.log (T.normalizedAbs x) : ℂ))) =
      (Complex.exp (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)))⁻¹ *
        Complex.exp (-s * (Real.log (T.normalizedAbs x) : ℂ)) := by
    rw [← Complex.exp_neg, ← Complex.exp_add]
    ring_nf
  rw [he]
  have hE := Complex.exp_ne_zero (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ))
  field_simp

theorem preimage_mul_gaussShell (b : F.Carrierˣ) (d : ℤ) :
    (fun x => (b : F.Carrier) * x) ⁻¹' gaussShell T d =
      gaussShell T (d + T.ord (b : F.Carrier)) := by
  ext x
  simp only [Set.mem_preimage, gaussShell, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h⟩
    have hx : x ≠ 0 := right_ne_zero_of_mul h0
    rw [T.ord_mul b.ne_zero hx] at h
    exact ⟨hx, by omega⟩
  · rintro ⟨hx, h⟩
    refine ⟨mul_ne_zero b.ne_zero hx, ?_⟩
    rw [T.ord_mul b.ne_zero hx]
    omega

/-- Changing the additive character by `x ↦ ψ(bx)` at a fixed Haar measure. -/
theorem epsilonAt_mulShift (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1) (χ : Character)
    (ψ : AddChar F.Carrier Circle) (μ : LocalHaar) {a : ℕ} (hχ : ConductorAt T χ a)
    (n : ℤ) (b : F.Carrierˣ) (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    epsilonAt T π χ (ψ.mulShift (b : F.Carrier)) μ.measure a (n + T.ord (b : F.Carrier)) s =
      (χ b : ℂ) *
        Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) *
        epsilonAt T π χ ψ μ.measure a n s := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hlog := log_normalizedAbs_unit T b
  unfold epsilonAt
  split_ifs with ha
  · subst ha
    rw [chi_eq_zpow_ord T χ hχ hπ b, hlog,
      zpow_add₀ (χ π).ne_zero]
    have he : Complex.exp (((n + T.ord (b : F.Carrier) : ℤ) : ℂ) * (1 - s) *
          (Real.log (T.residueCardinality : ℝ) : ℂ)) =
        Complex.exp ((s - 1) * ((-(T.ord (b : F.Carrier) : ℝ) *
          Real.log (T.residueCardinality : ℝ) : ℝ) : ℂ)) *
        Complex.exp ((n : ℂ) * (1 - s) * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      push_cast
      ring_nf
    rw [he]
    ring
  · set S := gaussShell T (n + (a : ℤ))
    set C := (χ b : ℂ) * Complex.exp (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ))
    have hshell : gaussShell T (n + T.ord (b : F.Carrier) + (a : ℤ)) =
        (fun x => (b : F.Carrier) * x) ⁻¹' S := by
      rw [preimage_mul_gaussShell]
      congr 1
      ring
    have hmap := HarmonicAnalysis.padicScalarHaarScaling F T μ.measure b
    have hsub := (Homeomorph.mulLeft₀ (b : F.Carrier) b.ne_zero).measurableEmbedding.setIntegral_map
      (μ := μ.measure) (fun y => C * gaussIntegrand T χ ψ s y) S
    have hb := T.normalizedAbs_pos b.ne_zero
    calc
      _ = ∫ x in (fun x => (b : F.Carrier) * x) ⁻¹' S,
          C * gaussIntegrand T χ ψ s ((b : F.Carrier) * x) ∂μ.measure := by
        rw [hshell]
        apply setIntegral_congr_fun
        · exact (gaussShell_measurableSet T _).preimage (measurable_const_mul _)
        intro x hx
        exact gaussIntegrand_mulShift T χ ψ b s (right_ne_zero_of_mul hx.1)
      _ = ∫ y in S, C * gaussIntegrand T χ ψ s y
          ∂μ.measure.map (fun x => (b : F.Carrier) * x) := hsub.symm
      _ = ((T.normalizedAbsUnits b : NNReal)⁻¹) •
          ∫ y in S, C * gaussIntegrand T χ ψ s y ∂μ.measure := by
        rw [hmap, Measure.restrict_smul, integral_smul_nnreal_measure]
      _ = _ := by
        rw [integral_const_mul, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
          T.normalizedAbsUnits_coe]
        have hinv : ((T.normalizedAbs (b : F.Carrier))⁻¹ : ℝ) =
            Real.exp (-Real.log (T.normalizedAbs (b : F.Carrier))) := by
          rw [Real.exp_neg, Real.exp_log hb]
        rw [hinv, Complex.ofReal_exp]
        simp only [C]
        have he : Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) =
            Complex.exp (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) *
              Complex.exp (((-Real.log (T.normalizedAbs (b : F.Carrier)) : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]
          push_cast
          ring_nf
        rw [he]
        ring

/-- Twisting by an unramified quasicharacter on the extension by zero. -/
theorem characterExtension_mul_unramified (χ ω : Character) (h0 : ConductorAt T ω 0)
    {π : F.Carrierˣ} (hπ : T.ord (π : F.Carrier) = 1) {x : F.Carrier} (hx : x ≠ 0) :
    characterExtension T (χ * ω) x = characterExtension T χ x * (ω π : ℂ) ^ T.ord x := by
  have h := chi_eq_zpow_ord T ω h0 hπ (Units.mk0 x hx)
  rw [Units.val_mk0] at h
  simp only [characterExtension, hx, dite_false, ContinuousMonoidHom.mul_apply, Units.val_mul,
    h]

/-- The unramified twist law for the epsilon expression at explicit levels. -/
theorem epsilonAt_mul_unramified (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ ω : Character) (h0 : ConductorAt T ω 0) (ψ : AddChar F.Carrier Circle)
    (μ : BorelMeasure T) (a : ℕ) (n : ℤ) (s : ℂ) :
    epsilonAt T π (χ * ω) ψ μ a n s =
      (ω π : ℂ) ^ (n + (a : ℤ)) * epsilonAt T π χ ψ μ a n s := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  unfold epsilonAt
  split_ifs with ha
  · subst ha
    simp only [ContinuousMonoidHom.mul_apply, Units.val_mul, mul_zpow, Nat.cast_zero, add_zero]
    ring
  · rw [← integral_const_mul]
    apply setIntegral_congr_fun (gaussShell_measurableSet T _)
    intro x hx
    simp only [gaussIntegrand]
    rw [characterExtension_mul_unramified T χ ω h0 hπ hx.1, hx.2, mul_inv, zpow_neg, inv_inv]
    ring

theorem spectralVariable_mul (s t : ℂ) :
    spectralVariable T t * spectralVariable T s = spectralVariable T (s + t) := by
  simp only [spectralVariable, ← Complex.exp_add]
  ring_nf

/-- An unramified twist shifts the Euler expression. -/
theorem lFactorAt_mul_unramified (π : F.Carrierˣ) (χ ω : Character) (a : ℕ) (t : ℂ)
    (ht : (ω π : ℂ) = spectralVariable T t) (s : ℂ) :
    lFactorAt T π (χ * ω) a s = lFactorAt T π χ a (s + t) := by
  let := T.topology
  unfold lFactorAt
  split_ifs with ha
  · rw [ContinuousMonoidHom.mul_apply, Units.val_mul, ht, mul_assoc, spectralVariable_mul]
  · rfl

/-- An unramified twist shifts the epsilon expression. -/
theorem epsilonAt_mul_unramified_shift (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ ω : Character) (h0 : ConductorAt T ω 0) (ψ : AddChar F.Carrier Circle)
    (μ : BorelMeasure T) (a : ℕ) (n : ℤ) (t : ℂ) (ht : (ω π : ℂ) = spectralVariable T t)
    (s : ℂ) :
    epsilonAt T π (χ * ω) ψ μ a n s = epsilonAt T π χ ψ μ a n (s + t) := by
  rw [epsilonAt_mul_unramified T π hπ χ ω h0 ψ μ a n s, ht,
    epsilonAt_eq_zero_mul T π χ ψ μ a n s, epsilonAt_eq_zero_mul T π χ ψ μ a n (s + t)]
  have hk : spectralVariable T t ^ (n + (a : ℤ)) =
      Complex.exp (((n + (a : ℤ) : ℤ) : ℂ) * (-t * (Real.log (T.residueCardinality : ℝ) : ℂ))) := by
    rw [spectralVariable, Complex.exp_int_mul]
  have he : Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * (s + t) *
        (Real.log (T.residueCardinality : ℝ) : ℂ)) =
      Complex.exp (((n + (a : ℤ) : ℤ) : ℂ) * (-t * (Real.log (T.residueCardinality : ℝ) : ℂ))) *
        Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    ring_nf
  rw [hk, he]
  ring

end Langlands.LocalFactor.PadicAbelian

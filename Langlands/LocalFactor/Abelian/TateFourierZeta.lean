import Langlands.LocalFactor.Abelian.TateGaussLattice

/-!
# Zeta integrals of Fourier transforms of lattice cosets

The plus Fourier transform of the coset `b + π^(-m) O` is
`μ(π^(-m) O) ψ(b y) 1_{π^(-(n-m)) O}(y)`. Its zeta integral for `χ⁻¹` at `1 - s`
is a lattice zeta integral when `b ∈ π^(-m) O`, and otherwise, after the
substitution `y ↦ b y`, a Gauss integral of `(χ, ψ)` over a lattice. The algebraic
identities closing the unramified functional equation are recorded separately.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "addCharOf" ψ =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter.toAddChar F.Carrier _ T.topology ψ

theorem zetaIntegrand_const_mul (c : ℂ) (g : F.Carrier → ℂ) (χ : Character) (s : ℂ) :
    zetaIntegrand T (fun y => c * g y) χ s = fun y => c * zetaIntegrand T g χ s y := by
  funext y
  unfold zetaIntegrand
  split_ifs <;> ring

theorem zeta_const_mul (μ : BorelMeasure T) (c : ℂ) (g : F.Carrier → ℂ) (χ : Character)
    (s : ℂ) : zeta T μ (fun y => c * g y) χ s = c * zeta T μ g χ s := by
  let := T.topology
  let := borel F.Carrier
  unfold zeta
  rw [zetaIntegrand_const_mul]
  exact integral_const_mul c _

/-- The zeta integral is linear on finite combinations with integrable zeta integrands. -/
theorem zeta_finset_sum {ι : Type*} (S : Finset ι) (c : ι → ℂ) (g : ι → F.Carrier → ℂ)
    (f : F.Carrier → ℂ) (hf : ∀ x, f x = ∑ i ∈ S, c i * g i x) (μ : BorelMeasure T)
    (χ : Character) (s : ℂ)
    (hg : ∀ i ∈ S,
      letI := T.topology
      letI := borel F.Carrier
      Integrable (zetaIntegrand T (g i) χ s) μ) :
    zeta T μ f χ s = ∑ i ∈ S, c i * zeta T μ (g i) χ s := by
  let := T.topology
  let := borel F.Carrier
  have hpt : zetaIntegrand T f χ s =
      fun x => ∑ i ∈ S, c i * zetaIntegrand T (g i) χ s x := by
    funext x
    unfold zetaIntegrand
    split_ifs
    · simp
    · rw [hf x, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
  unfold zeta
  rw [hpt, integral_finsetSum _ (fun i hi => (hg i hi).const_mul (c i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_const_mul (c i) _

/-- The Fourier transform of a lattice containing the centre: a multiple of the dual
lattice indicator. -/
theorem zeta_fourierCoset_of_mem (μ : LocalHaar) (ψ : AdditiveCharacter) (χ : Character)
    (s : ℂ) (c : ℂ) (m : ℤ) {b : F.Carrier} (hb : b ∈ T.additiveLattice m) :
    letI := T.topology
    letI := borel F.Carrier
    zeta T μ.measure (fun y => c * ψ.complex (b * y) *
        (T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier).indicator
          (fun _ => (1 : ℂ)) y) χ s =
      c * zeta T μ.measure ((T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier).indicator
          (fun _ => (1 : ℂ))) χ s := by
  let := T.topology
  let := borel F.Carrier
  rw [← zeta_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ (T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier)
  · have h1 := (T.forall_mul_eq_one_iff_mem_additiveLattice ψ m y).mpr hy b hb
    simp only [Set.indicator_of_mem hy, HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
      h1, Circle.coe_one, mul_one]
  · simp only [Set.indicator_of_notMem hy, mul_zero]

/-- The Fourier transform of a coset with unit centre `b`: after `y ↦ b y` its zeta integral
for `χ⁻¹` at `1 - s` is a Gauss integral of `(χ, ψ)` over a lattice. -/
theorem zeta_fourierCoset_unit (μ : LocalHaar) (ψ : AdditiveCharacter) (χ : Character)
    (s : ℂ) (c : ℂ) (L : ℤ) (b : F.Carrierˣ) :
    letI := T.topology
    letI := borel F.Carrier
    zeta T μ.measure (fun y => c * ψ.complex ((b : F.Carrier) * y) *
        (T.additiveLattice L : Set F.Carrier).indicator (fun _ => (1 : ℂ)) y) χ⁻¹ (1 - s) =
      c * ((χ b : ℂ) * Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) *
        ∫ x in (T.additiveLattice (L - T.ord (b : F.Carrier)) : Set F.Carrier),
          gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  set Lset := (T.additiveLattice L : Set F.Carrier) with hLset
  have hb0 := b.ne_zero
  have hbp := T.normalizedAbs_pos hb0
  set K : ℂ := (χ b : ℂ) * Complex.exp (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ))
    with hK
  have hpt : zetaIntegrand T (fun y => c * ψ.complex ((b : F.Carrier) * y) *
      Lset.indicator (fun _ => (1 : ℂ)) y) χ⁻¹ (1 - s) =
      Lset.indicator (fun y => c * (K * gaussIntegrand T χ ψ.toAddChar s ((b : F.Carrier) * y))) := by
    funext y
    by_cases hy : y ∈ Lset
    · rw [Set.indicator_of_mem hy]
      by_cases h0 : y = 0
      · subst h0
        simp [zetaIntegrand, gaussIntegrand, characterExtension]
      · have hyp := T.normalizedAbs_pos h0
        simp only [zetaIntegrand, h0, ite_false, Set.indicator_of_mem hy, mul_one,
          gaussIntegrand, characterExtension_unit_mul, characterExtension_inv,
          T.normalizedAbs_mul, Real.log_mul hbp.ne' hyp.ne', Complex.ofReal_add,
          HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, hK, mul_inv]
        have hE : Complex.exp (-s * ((Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ) +
            (Real.log (T.normalizedAbs y) : ℂ))) =
            (Complex.exp (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)))⁻¹ *
              Complex.exp ((1 - s - 1) * (Real.log (T.normalizedAbs y) : ℂ)) := by
          rw [← Complex.exp_neg, ← Complex.exp_add]
          ring_nf
        rw [hE]
        have hχb := (χ b).ne_zero
        have hEb := Complex.exp_ne_zero (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ))
        field_simp
    · rw [Set.indicator_of_notMem hy]
      simp [zetaIntegrand, Set.indicator_of_notMem hy]
  have hpre : (fun y => (b : F.Carrier) * y) ⁻¹'
      (T.additiveLattice (L - T.ord (b : F.Carrier)) : Set F.Carrier) = Lset := by
    rw [preimage_mul_additiveLattice, sub_add_cancel]
  have hsub := setIntegral_preimage_mul_unit T μ b
    (T.additiveLattice (L - T.ord (b : F.Carrier)) : Set F.Carrier)
    (gaussIntegrand T χ ψ.toAddChar s)
  rw [hpre] at hsub
  have hz : zeta T μ.measure (fun y => c * ψ.complex ((b : F.Carrier) * y) *
      Lset.indicator (fun _ => (1 : ℂ)) y) χ⁻¹ (1 - s) =
      ∫ y in Lset, c * (K * gaussIntegrand T χ ψ.toAddChar s ((b : F.Carrier) * y)) ∂μ.measure := by
    rw [← integral_indicator (additiveLattice_measurableSet T L), ← hpt]
    rfl
  rw [hz, integral_const_mul, integral_const_mul, hsub, Complex.real_smul]
  have hinv : (((T.normalizedAbs (b : F.Carrier))⁻¹ : ℝ) : ℂ) =
      Complex.exp (-(Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hbp]
  rw [hinv, hK]
  have he : Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) =
      Complex.exp (s * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) *
        Complex.exp (-(Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) := by
    rw [← Complex.exp_add]
    ring_nf
  rw [he]
  ring

/-- The algebra closing the unramified functional equation on a lattice. -/
theorem fe_algebra_lattice {c r u V μO : ℂ} (hc : c ≠ 0) (hr : r ≠ 0) (hu : u ≠ 0) (n m : ℤ)
    (hX : 1 - c * u ≠ 0) (hY : 1 - c⁻¹ * (r⁻¹ * u⁻¹) ≠ 0) :
    r ^ m * μO * ((1 - c⁻¹ * (r⁻¹ * u⁻¹))⁻¹ * (c⁻¹ * (r⁻¹ * u⁻¹)) ^ (-(n - m)) * V) *
        (1 - c⁻¹ * (r⁻¹ * u⁻¹)) =
      c ^ n * (r * u) ^ n * μO * ((1 - c * u)⁻¹ * (c * u) ^ (-m) * V) * (1 - c * u) := by
  have e1 : (c⁻¹ * (r⁻¹ * u⁻¹)) ^ (-(n - m)) =
      c ^ n / c ^ m * (r ^ n / r ^ m * (u ^ n / u ^ m)) := by
    simp only [mul_zpow, inv_zpow, zpow_neg, mul_inv, inv_inv, zpow_sub₀ hc, zpow_sub₀ hr,
      zpow_sub₀ hu]
  have e2 : (c * u) ^ (-m) = (c ^ m)⁻¹ * (u ^ m)⁻¹ := by
    rw [mul_zpow, zpow_neg, zpow_neg]
  have hY' : c * r * u - 1 ≠ 0 := by
    intro h
    apply hY
    have h1 : c * r * u = 1 := by linear_combination h
    rw [show c⁻¹ * (r⁻¹ * u⁻¹) = (c * r * u)⁻¹ by simp only [mul_inv]; ring, h1, inv_one,
      sub_self]
  rw [e1, e2, mul_zpow]
  have hcm := zpow_ne_zero m hc
  have hrm := zpow_ne_zero m hr
  have hum := zpow_ne_zero m hu
  field_simp

/-- The algebra closing the unramified functional equation off the lattice. -/
theorem fe_algebra_shell {c r u μO : ℂ} (hc : c ≠ 0) (hr : r ≠ 0) (hu : u ≠ 0) (n : ℤ)
    (hY : 1 - c⁻¹ * (r⁻¹ * u⁻¹) ≠ 0) :
    ((1 - c⁻¹ * (r⁻¹ * u⁻¹))⁻¹ * (c⁻¹ * (r⁻¹ * u⁻¹)) ^ (-n) * ((1 - r⁻¹) * μO) -
        (c * u) ^ (n + 1) * (r ^ n * μO)) * (1 - c⁻¹ * (r⁻¹ * u⁻¹)) =
      c ^ n * (r * u) ^ n * μO * (1 - c * u) := by
  have e1 : (c⁻¹ * (r⁻¹ * u⁻¹)) ^ (-n) = c ^ n * (r ^ n * u ^ n) := by
    simp only [mul_zpow, inv_zpow, zpow_neg, mul_inv, inv_inv]
  have e2 : (c * u) ^ (n + 1) = c ^ n * u ^ n * (c * u) := by
    rw [zpow_add_one₀ (mul_ne_zero hc hu), mul_zpow]
  have hY' : c * r * u - 1 ≠ 0 := by
    intro h
    apply hY
    have h1 : c * r * u = 1 := by linear_combination h
    rw [show c⁻¹ * (r⁻¹ * u⁻¹) = (c * r * u)⁻¹ by simp only [mul_inv]; ring, h1, inv_one,
      sub_self]
  rw [e1, e2, mul_zpow]
  field_simp
  ring

end Langlands.LocalFactor.PadicAbelian

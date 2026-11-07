import Langlands.LocalFactor.Abelian.GaussEpsilon

/-!
# Vanishing of ramified Gauss integrals off the conductor shell

For a quasicharacter of positive conductor `a` and an additive character trivial on
the lattice of level `m`, the Gauss integral over the shell of order `-d` vanishes
when `d < m + a` (rotation by a principal unit) and, if the character is nontrivial
on the lattice of level `m + 1`, also when `d > m + a` (translation).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

theorem gauss_valuation_eq_exp_neg_ord {x : F.Carrier} (hx : x ≠ 0) :
    T.discreteValuation x = WithZero.exp (-T.ord x) := by
  have hv : T.discreteValuation x ≠ 0 := (map_ne_zero _).mpr hx
  simp only [PadicField.TopologicalData.ord, neg_neg]
  exact (WithZero.exp_log hv).symm

theorem gauss_valuation_le_exp_iff {x : F.Carrier} (hx : x ≠ 0) (k : ℤ) :
    T.discreteValuation x ≤ WithZero.exp k ↔ -k ≤ T.ord x := by
  rw [gauss_valuation_eq_exp_neg_ord T hx, WithZero.exp_le_exp]
  omega

theorem mem_gaussShell_iff_valuation (d : ℤ) (x : F.Carrier) :
    x ∈ gaussShell T d ↔ T.discreteValuation x = WithZero.exp d := by
  rw [gaussShell_eq_valuationShell]
  rfl

/-- Rotating a shell by a unit of order zero preserves its Haar integrals. -/
theorem setIntegral_gaussShell_mul_unit (μ : LocalHaar) (u : F.Carrierˣ)
    (hu : T.ord (u : F.Carrier) = 0) (d : ℤ) (g : F.Carrier → ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x in gaussShell T d, g ((u : F.Carrier) * x) ∂μ.measure =
      ∫ x in gaussShell T d, g x ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hpre : (fun x => (u : F.Carrier) * x) ⁻¹' gaussShell T d = gaussShell T d := by
    rw [preimage_mul_gaussShell, hu, add_zero]
  have hmap := HarmonicAnalysis.padicScalarHaarScaling F T μ.measure u
  have habs : T.normalizedAbsUnits u = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    rw [T.normalizedAbsUnits_coe, T.normalizedAbs_of_ne_zero u.ne_zero, hu]
    simp
  have hsub := (Homeomorph.mulLeft₀ (u : F.Carrier) u.ne_zero).measurableEmbedding.setIntegral_map
    (μ := μ.measure) g (gaussShell T d)
  calc
    _ = ∫ x in (fun x => (u : F.Carrier) * x) ⁻¹' gaussShell T d,
        g ((u : F.Carrier) * x) ∂μ.measure := by rw [hpre]
    _ = ∫ y in gaussShell T d, g y ∂μ.measure.map (fun x => (u : F.Carrier) * x) := hsub.symm
    _ = _ := by rw [hmap, habs, Units.val_one, inv_one, one_smul]

/-- Translating a shell by an element of strictly smaller valuation preserves its
Haar integrals. -/
theorem setIntegral_gaussShell_add (μ : LocalHaar) (d : ℤ) (x₀ : F.Carrier)
    (hx₀ : T.discreteValuation x₀ < WithZero.exp d) (g : F.Carrier → ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x in gaussShell T d, g (x₀ + x) ∂μ.measure =
      ∫ x in gaussShell T d, g x ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hpre : (fun x => x₀ + x) ⁻¹' gaussShell T d = gaussShell T d := by
    ext x
    simp only [Set.mem_preimage, mem_gaussShell_iff_valuation]
    constructor
    · intro h
      have hlt : T.discreteValuation (-x₀) < T.discreteValuation (x₀ + x) := by
        rw [Valuation.map_neg, h]
        exact hx₀
      have := T.discreteValuation.map_add_eq_of_lt_left hlt
      rw [show x₀ + x + -x₀ = x by ring, h] at this
      exact this
    · intro h
      rw [T.discreteValuation.map_add_eq_of_lt_right (h ▸ hx₀), h]
  have hmp := measurePreserving_add_left μ.measure x₀
  have hemb := (Homeomorph.addLeft x₀).measurableEmbedding
  have := hmp.setIntegral_preimage_emb hemb g (gaussShell T d)
  rw [hpre] at this
  exact this

/-- The unshifted Gauss integrand on a shell. -/
theorem gaussIntegrand_zero_apply (χ : Character) (ψ : AddChar F.Carrier Circle)
    (x : F.Carrier) :
    gaussIntegrand T χ ψ 0 x = (characterExtension T χ x)⁻¹ * (ψ x : ℂ) := by
  simp [gaussIntegrand]

private theorem eq_zero_of_eq_mul_ne_one {I c : ℂ} (h : I = c * I) (hc : c ≠ 1) : I = 0 := by
  have h' : (1 - c) * I = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact absurd (sub_eq_zero.mp h1).symm hc
  · exact h1

/-- Below the conductor shell the Gauss integral vanishes, by rotation with a principal
unit on which the quasicharacter is nontrivial. -/
theorem gauss_shell_integral_eq_zero_of_lt (μ : LocalHaar) (χ : Character) {a : ℕ}
    (hχ : ConductorAt T χ a) (ha : a ≠ 0) (ψ : AddChar F.Carrier Circle) (m : ℤ)
    (hψ : ∀ x : F.Carrier, T.discreteValuation x ≤ WithZero.exp m → ψ x = 1)
    (d : ℤ) (hd : d < m + a) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x in gaussShell T d, gaussIntegrand T χ ψ 0 x ∂μ.measure = 0 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  set k : ℕ := (d - m).toNat with hk
  have hka : k < T.multiplicativeConductor χ := by
    rw [← (conductorAt_iff T χ a).mp hχ]
    omega
  obtain ⟨u, hu, hχu⟩ := T.exists_nontrivial_below_multiplicativeConductor χ k hka
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hχu (map_one χ)
  have hu1' : (u : F.Carrier) - 1 ≠ 0 := by
    intro h
    exact hu1 (Units.ext (sub_eq_zero.mp h))
  have hord : T.ord (u : F.Carrier) = 0 := by
    have := hu.1
    rw [gauss_valuation_eq_exp_neg_ord T u.ne_zero, ← WithZero.exp_zero] at this
    have := WithZero.exp_injective this
    omega
  have hord1 : (k : ℤ) ≤ T.ord ((u : F.Carrier) - 1) := by
    have := (gauss_valuation_le_exp_iff T hu1' _).mp hu.2
    omega
  have hrot : ∀ x ∈ gaussShell T d,
      gaussIntegrand T χ ψ 0 ((u : F.Carrier) * x) =
        ((χ u : ℂ))⁻¹ * gaussIntegrand T χ ψ 0 x := by
    intro x hx
    rw [gaussIntegrand_zero_apply, gaussIntegrand_zero_apply, characterExtension_unit_mul]
    have hψu : ψ ((u : F.Carrier) * x) = ψ x := by
      have hsplit : (u : F.Carrier) * x = x + ((u : F.Carrier) - 1) * x := by ring
      have htriv : ψ (((u : F.Carrier) - 1) * x) = 1 := by
        apply hψ
        rw [gauss_valuation_le_exp_iff T (mul_ne_zero hu1' hx.1),
          T.ord_mul hu1' hx.1, hx.2]
        omega
      rw [hsplit, AddChar.map_add_eq_mul, htriv, mul_one]
    rw [hψu, mul_inv]
    ring
  have hI : ∫ x in gaussShell T d, gaussIntegrand T χ ψ 0 x ∂μ.measure =
      ((χ u : ℂ))⁻¹ * ∫ x in gaussShell T d, gaussIntegrand T χ ψ 0 x ∂μ.measure := by
    conv_lhs => rw [← setIntegral_gaussShell_mul_unit T μ u hord d]
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (gaussShell_measurableSet T d) hrot
  refine eq_zero_of_eq_mul_ne_one hI ?_
  intro h
  apply hχu
  apply Units.ext
  rw [Units.val_one]
  exact inv_eq_one.mp h

/-- Above the conductor shell the Gauss integral vanishes, by translation with an
element of the next lattice on which the additive character is nontrivial. -/
theorem gauss_shell_integral_eq_zero_of_gt (μ : LocalHaar) (χ : Character) {a : ℕ}
    (hχ : ConductorAt T χ a) (ha : a ≠ 0) (ψ : AddChar F.Carrier Circle) (m : ℤ)
    (x₀ : F.Carrier) (hx₀ : T.discreteValuation x₀ ≤ WithZero.exp (m + 1)) (hψx₀ : ψ x₀ ≠ 1)
    (d : ℤ) (hd : m + a < d) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x in gaussShell T d, gaussIntegrand T χ ψ 0 x ∂μ.measure = 0 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hψx₀ (AddChar.map_zero_eq_one ψ)
  have hordx₀ : -(m + 1) ≤ T.ord x₀ := (gauss_valuation_le_exp_iff T hx₀0 _).mp hx₀
  have hlt : T.discreteValuation x₀ < WithZero.exp d :=
    hx₀.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
  have htr : ∀ x ∈ gaussShell T d,
      gaussIntegrand T χ ψ 0 (x₀ + x) = (ψ x₀ : ℂ) * gaussIntegrand T χ ψ 0 x := by
    intro x hx
    have hx0 := hx.1
    set w : F.Carrier := 1 + x₀ / x with hw
    have hw1 : w - 1 ≠ 0 := by
      rw [hw, add_sub_cancel_left]
      exact div_ne_zero hx₀0 hx0
    have hordw1 : (a : ℤ) ≤ T.ord (w - 1) := by
      rw [hw, add_sub_cancel_left, div_eq_mul_inv, T.ord_mul hx₀0 (inv_ne_zero hx0),
        T.ord_inv, hx.2]
      omega
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, zero_sub, ← neg_one_mul, T.ord_mul (by norm_num) one_ne_zero] at hordw1
      have h1 : T.ord (-1 : F.Carrier) = 0 := by
        have := T.ord_mul (x := (-1 : F.Carrier)) (y := -1) (by norm_num) (by norm_num)
        rw [neg_one_mul, neg_neg, T.ord_one] at this
        omega
      rw [h1, T.ord_one] at hordw1
      omega
    have hlevel : unitLevel T a (Units.mk0 w hw0) := by
      simp only [unitLevel, ha, ite_false, Units.val_mk0]
      rw [gauss_valuation_le_exp_iff T hw1]
      omega
    have hχw : (χ (Units.mk0 w hw0) : ℂ) = 1 := by
      rw [hχ.1 _ hlevel, Units.val_one]
    have hsum : x₀ + x = ((Units.mk0 w hw0 : F.Carrierˣ) : F.Carrier) * x := by
      rw [Units.val_mk0, hw]
      field_simp
      ring
    have hchar : characterExtension T χ (x₀ + x) = characterExtension T χ x := by
      rw [hsum, characterExtension_unit_mul, hχw, one_mul]
    rw [gaussIntegrand_zero_apply, gaussIntegrand_zero_apply, hchar, AddChar.map_add_eq_mul,
      Circle.coe_mul]
    ring
  have hI : ∫ x in gaussShell T d, gaussIntegrand T χ ψ 0 x ∂μ.measure =
      (ψ x₀ : ℂ) * ∫ x in gaussShell T d, gaussIntegrand T χ ψ 0 x ∂μ.measure := by
    conv_lhs => rw [← setIntegral_gaussShell_add T μ d x₀ hlt]
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (gaussShell_measurableSet T d) htr
  refine eq_zero_of_eq_mul_ne_one hI ?_
  intro h
  exact hψx₀ (Subtype.ext (by simpa using h))

/-- A ramified Gauss integral vanishes on every shell other than the conductor shell. -/
theorem gauss_shell_integral_eq_zero (μ : LocalHaar) (χ : Character) {a : ℕ}
    (hχ : ConductorAt T χ a) (ha : a ≠ 0) (ψ : AddChar F.Carrier Circle) {n : ℤ}
    (hψ : AdditiveConductorAt T ψ n) (d : ℤ) (hd : d ≠ n + a) (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x in gaussShell T d, gaussIntegrand T χ ψ s x ∂μ.measure = 0 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have h0 : ∫ x in gaussShell T d, gaussIntegrand T χ ψ 0 x ∂μ.measure = 0 := by
    rcases lt_or_gt_of_ne hd with hlt | hgt
    · exact gauss_shell_integral_eq_zero_of_lt T μ χ hχ ha ψ n hψ.1 d hlt
    · obtain ⟨x₀, hx₀, hψx₀⟩ : ∃ x₀ : F.Carrier,
          T.discreteValuation x₀ ≤ WithZero.exp (n + 1) ∧ ψ x₀ ≠ 1 := by
        by_contra hc
        push Not at hc
        have := hψ.2 hc
        omega
      exact gauss_shell_integral_eq_zero_of_gt T μ χ hχ ha ψ n x₀ hx₀ hψx₀ d hgt
  have hcongr : ∫ x in gaussShell T d, gaussIntegrand T χ ψ s x ∂μ.measure =
      ∫ x in gaussShell T d, gaussIntegrand T χ ψ 0 x *
        Complex.exp (-(d : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)) ∂μ.measure :=
    setIntegral_congr_fun (gaussShell_measurableSet T d)
      (fun x hx => gaussIntegrand_on_shell_spectral T χ ψ d s hx)
  rw [hcongr, integral_mul_const, h0, zero_mul]

end Langlands.LocalFactor.PadicAbelian

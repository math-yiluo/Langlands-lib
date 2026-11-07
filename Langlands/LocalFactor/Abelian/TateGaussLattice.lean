import Langlands.LocalFactor.Abelian.TateLatticeZeta
import Langlands.HarmonicAnalysis.PadicLatticeFourierProof

/-!
# Gauss integrals over valuation lattices

For an additive character `ψ` of conductor `n` the integral of `ψ` over the
lattice `π^(-M) O` is its mass for `M ≤ n` and zero otherwise. The Gauss
integrand of `(χ, ψ)` agrees with the zeta integrand of `χ⁻¹` at `1 - s` on
`π^(-n) O`; its integral over `π^(-(n+j)) O` is computed shell by shell: in the
ramified case only the conductor shell contributes, and in the unramified case
only the shell of order `-(n+1)` is added to the lattice tail.
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

theorem preimage_mul_additiveLattice (b : F.Carrierˣ) (d : ℤ) :
    (fun x => (b : F.Carrier) * x) ⁻¹' (T.additiveLattice d : Set F.Carrier) =
      (T.additiveLattice (d + T.ord (b : F.Carrier)) : Set F.Carrier) := by
  ext x
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [Set.mem_preimage, SetLike.mem_coe, T.mem_additiveLattice,
      gauss_valuation_le_exp_iff T (mul_ne_zero b.ne_zero hx), gauss_valuation_le_exp_iff T hx,
      T.ord_mul b.ne_zero hx]
    omega

theorem additiveLattice_succ_eq_union (M : ℤ) :
    (T.additiveLattice (M + 1) : Set F.Carrier) =
      (T.additiveLattice M : Set F.Carrier) ∪ gaussShell T (M + 1) := by
  ext x
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [Set.mem_union, SetLike.mem_coe, T.mem_additiveLattice,
      gauss_valuation_le_exp_iff T hx, gaussShell, Set.mem_ofPred_eq, ne_eq, hx,
      not_false_eq_true, true_and]
    omega

theorem disjoint_additiveLattice_gaussShell (M : ℤ) :
    Disjoint (T.additiveLattice M : Set F.Carrier) (gaussShell T (M + 1)) := by
  refine Set.disjoint_left.mpr fun x hx hs => ?_
  have h1 := (gauss_valuation_le_exp_iff T hs.1 M).mp hx
  have h2 := hs.2
  omega

theorem additiveLattice_measurableSet (M : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    MeasurableSet (T.additiveLattice M : Set F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  exact (T.isOpen_additiveLattice M).measurableSet

/-- The integral of an additive character over a valuation lattice. -/
theorem setIntegral_additiveLattice_character (μ : LocalHaar) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (M : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in (T.additiveLattice M : Set F.Carrier), (ψ x : ℂ) ∂μ.measure =
      if M ≤ n then ((μ.measure (T.additiveLattice M : Set F.Carrier)).toReal : ℂ) else 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hrw : ∫ x in (T.additiveLattice M : Set F.Carrier), (ψ x : ℂ) ∂μ.measure =
      ∫ t, ψ.complex (t * 1) *
        (T.additiveLattice M : Set F.Carrier).indicator (fun _ => (1 : ℂ)) t ∂μ.measure := by
    rw [← integral_indicator (additiveLattice_measurableSet T M)]
    congr 1
    funext t
    by_cases ht : t ∈ (T.additiveLattice M : Set F.Carrier)
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  rw [hrw]
  split_ifs with hM
  · exact HarmonicAnalysis.subgroup_character_integral_of_trivial ψ μ _
      (T.isOpen_additiveLattice M) 1
      (fun t ht => by rw [mul_one]; exact hψ.1 t ((T.additiveLattice_mono hM) ht))
  · obtain ⟨x₀, hx₀, hψx₀⟩ : ∃ x₀ : F.Carrier,
        T.discreteValuation x₀ ≤ WithZero.exp (n + 1) ∧ ψ x₀ ≠ 1 := by
      by_contra hc
      push Not at hc
      have := hψ.2 hc
      omega
    exact HarmonicAnalysis.subgroup_character_integral_of_nontrivial ψ μ _ 1 x₀
      ((T.additiveLattice_mono (show n + 1 ≤ M by omega)) hx₀) (by rwa [mul_one])

theorem gaussShell_isCompact (d : ℤ) :
    letI := T.topology
    IsCompact (gaussShell T d) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [gaussShell_eq_valuationShell]
  exact (T.valuationShell_compact_closed d).1

/-- The integral of an additive character over a shell is a difference of lattice
integrals. -/
theorem setIntegral_gaussShell_character (μ : LocalHaar) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (D : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in gaussShell T D, (ψ x : ℂ) ∂μ.measure =
      (if D ≤ n then ((μ.measure (T.additiveLattice D : Set F.Carrier)).toReal : ℂ) else 0) -
        (if D - 1 ≤ n then ((μ.measure (T.additiveLattice (D - 1) : Set F.Carrier)).toReal : ℂ)
          else 0) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hcont : Continuous (fun x : F.Carrier => (ψ x : ℂ)) := ψ.continuous_complex
  have hL : IntegrableOn (fun x : F.Carrier => (ψ x : ℂ))
      (T.additiveLattice (D - 1) : Set F.Carrier) μ.measure :=
    hcont.continuousOn.integrableOn_compact' (T.isCompact_additiveLattice _)
      (additiveLattice_measurableSet T _)
  have hS : IntegrableOn (fun x : F.Carrier => (ψ x : ℂ)) (gaussShell T (D - 1 + 1)) μ.measure :=
    hcont.continuousOn.integrableOn_compact' (gaussShell_isCompact T _)
      (gaussShell_measurableSet T _)
  have hu := setIntegral_union (disjoint_additiveLattice_gaussShell T (D - 1))
    (gaussShell_measurableSet T _) hL hS
  rw [← additiveLattice_succ_eq_union, sub_add_cancel] at hu
  rw [← setIntegral_additiveLattice_character T μ ψ hψ D,
    ← setIntegral_additiveLattice_character T μ ψ hψ (D - 1), hu]
  ring

/-- On `π^(-M) O` with `M ≤ n` the Gauss integrand of `(χ, ψ)` at `s` is the zeta
integrand of the lattice indicator for `χ⁻¹` at `1 - s`. -/
theorem indicator_gaussIntegrand_eq_zetaIntegrand (χ : Character) (ψ : AddChar F.Carrier Circle)
    {n : ℤ} (hψ : AdditiveConductorAt T ψ n) {M : ℤ} (hM : M ≤ n) (s : ℂ) :
    (T.additiveLattice M : Set F.Carrier).indicator (gaussIntegrand T χ ψ s) =
      zetaIntegrand T ((T.additiveLattice M : Set F.Carrier).indicator (fun _ => (1 : ℂ)))
        χ⁻¹ (1 - s) := by
  funext x
  by_cases hx : x ∈ (T.additiveLattice M : Set F.Carrier)
  · rw [Set.indicator_of_mem hx]
    have hx' : T.discreteValuation x ≤ WithZero.exp M := hx
    have hψx : ψ x = 1 := hψ.1 x (hx'.trans (WithZero.exp_le_exp.mpr hM))
    by_cases h0 : x = 0
    · subst h0
      simp [zetaIntegrand, gaussIntegrand, characterExtension]
    · simp only [zetaIntegrand, gaussIntegrand, h0, ite_false, Set.indicator_of_mem hx,
        hψx, characterExtension_inv, Circle.coe_one, one_mul, mul_one]
      rw [show (1 - s - 1 : ℂ) = -s by ring]
  · rw [Set.indicator_of_notMem hx]
    simp [zetaIntegrand, Set.indicator_of_notMem hx]

/-- The Gauss integrand is integrable on every lattice `π^(-(n+j)) O` once the zeta
integral of `χ⁻¹` converges at `1 - s`. -/
theorem gaussIntegrand_integrableOn_additiveLattice (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (μ : LocalHaar) {s : ℂ}
    (hs : ConvergesAt T π χ⁻¹ (1 - s)) (j : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    IntegrableOn (gaussIntegrand T χ ψ.toAddChar s)
      (T.additiveLattice (n + j) : Set F.Carrier) μ.measure := by
  let := T.topology
  let := borel F.Carrier
  induction j with
  | zero =>
    have h := zeta_integrable T π hπ χ⁻¹ μ (cosetTest T n 0) (1 - s) hs
    rw [cosetTest_coe, coset_zero,
      ← indicator_gaussIntegrand_eq_zetaIntegrand T χ ψ.toAddChar hψ le_rfl s] at h
    simpa using (integrable_indicator_iff (additiveLattice_measurableSet T n)).mp h
  | succ j ih =>
    rw [show n + ((j + 1 : ℕ) : ℤ) = (n + j) + 1 by push_cast; ring,
      additiveLattice_succ_eq_union]
    exact ih.union (gaussIntegrand_integrable T χ ψ μ _ s)

/-- Adding one shell to a lattice Gauss integral. -/
theorem setIntegral_additiveLattice_succ_gauss (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (μ : LocalHaar) {s : ℂ}
    (hs : ConvergesAt T π χ⁻¹ (1 - s)) (j : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in (T.additiveLattice (n + j + 1) : Set F.Carrier),
        gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure =
      ∫ x in (T.additiveLattice (n + j) : Set F.Carrier),
          gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure +
        ∫ x in gaussShell T (n + j + 1), gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure := by
  let := T.topology
  let := borel F.Carrier
  rw [additiveLattice_succ_eq_union]
  exact setIntegral_union (disjoint_additiveLattice_gaussShell T _)
    (gaussShell_measurableSet T _)
    (gaussIntegrand_integrableOn_additiveLattice T π hπ χ ψ hψ μ hs j)
    (gaussIntegrand_integrable T χ ψ μ _ s)

/-- The lattice Gauss integral at the conductor level is the lattice zeta integral of
`χ⁻¹` at `1 - s`. -/
theorem setIntegral_additiveLattice_gauss_base (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (μ : LocalHaar) {s : ℂ}
    (hs : ConvergesAt T π χ⁻¹ (1 - s)) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in (T.additiveLattice n : Set F.Carrier),
        gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure =
      (1 - (χ⁻¹ π : ℂ) * spectralVariable T (1 - s))⁻¹ *
        ((χ⁻¹ π : ℂ) * spectralVariable T (1 - s)) ^ (-n) *
          ∫ x in integralUnits T, characterExtension T χ⁻¹ x ∂μ.measure := by
  let := T.topology
  let := borel F.Carrier
  rw [← zeta_additiveLattice T π hπ χ⁻¹ μ hs n,
    ← integral_indicator (additiveLattice_measurableSet T n),
    indicator_gaussIntegrand_eq_zetaIntegrand T χ ψ.toAddChar hψ le_rfl s]
  rfl

/-- In the ramified case the Gauss integral over `π^(-(n+j)) O` is the epsilon
expression when `a ≤ j` and zero otherwise. -/
theorem setIntegral_additiveLattice_gauss_ramified (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) {a : ℕ} (hχ : ConductorAt T χ a)
    (ha : a ≠ 0) (ψ : AdditiveCharacter) {n : ℤ}
    (hψ : AdditiveConductorAt T (addCharOf ψ) n) (μ : LocalHaar) {s : ℂ}
    (hs : ConvergesAt T π χ⁻¹ (1 - s)) (j : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in (T.additiveLattice (n + j) : Set F.Carrier),
        gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure =
      if a ≤ j then epsilonAt T π χ ψ.toAddChar μ.measure a n s else 0 := by
  let := T.topology
  let := borel F.Carrier
  induction j with
  | zero =>
    rw [ite_eq_right (by omega), Nat.cast_zero, add_zero,
      setIntegral_additiveLattice_gauss_base T π hπ χ ψ hψ μ hs,
      setIntegral_integralUnits_characterExtension T μ χ⁻¹ (conductorAt_inv T χ a hχ),
      ite_eq_right ha, mul_zero]
  | succ j ih =>
    rw [show n + ((j + 1 : ℕ) : ℤ) = n + j + 1 by push_cast; ring,
      setIntegral_additiveLattice_succ_gauss T π hπ χ ψ hψ μ hs j, ih]
    by_cases hja : j + 1 = a
    · rw [ite_eq_right (by omega), ite_eq_left (by omega), zero_add]
      unfold epsilonAt
      rw [ite_eq_right ha, show n + (j : ℤ) + 1 = n + a by omega]
    · rw [gauss_shell_integral_eq_zero T μ χ hχ ha ψ.toAddChar hψ (n + j + 1) (by omega) s,
        add_zero]
      by_cases haj : a ≤ j
      · rw [ite_eq_left haj, ite_eq_left (by omega)]
      · rw [ite_eq_right haj, ite_eq_right (by omega)]

/-- For an unramified quasicharacter the Gauss integrand on the shell of order `-D` is
`(χ(π) q^(-s))^D ψ`. -/
theorem setIntegral_gaussShell_unramified (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ : Character) (h0 : ConductorAt T χ 0) (ψ : AddChar F.Carrier Circle) (μ : LocalHaar)
    (s : ℂ) (D : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in gaussShell T D, gaussIntegrand T χ ψ s x ∂μ.measure =
      ((χ π : ℂ) * spectralVariable T s) ^ D * ∫ x in gaussShell T D, (ψ x : ℂ) ∂μ.measure := by
  let := T.topology
  let := borel F.Carrier
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (gaussShell_measurableSet T D)
  intro x hx
  have hx0 : x ≠ 0 := hx.1
  rw [gaussIntegrand_on_shell_spectral T χ ψ D s hx, gaussIntegrand_zero_apply]
  have hc : characterExtension T χ x = (χ π : ℂ) ^ (-D) := by
    have h := chi_eq_zpow_ord T χ h0 hπ (Units.mk0 x hx0)
    simp only [Units.val_mk0, hx.2] at h
    simp only [characterExtension, hx0, dite_false, h]
  rw [hc, mul_zpow, spectralVariable, ← Complex.exp_int_mul, zpow_neg, inv_inv]
  ring_nf

/-- In the unramified case the lattice Gauss integral beyond the conductor level adds
only the shell of order `-(n+1)`. -/
theorem setIntegral_additiveLattice_gauss_unramified (π : F.Carrierˣ)
    (hπ : T.ord (π : F.Carrier) = 1) (χ : Character) (h0 : ConductorAt T χ 0)
    (ψ : AdditiveCharacter) {n : ℤ} (hψ : AdditiveConductorAt T (addCharOf ψ) n)
    (μ : LocalHaar) {s : ℂ} (hs : ConvergesAt T π χ⁻¹ (1 - s)) (j : ℕ) (hj : 1 ≤ j) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in (T.additiveLattice (n + j) : Set F.Carrier),
        gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure =
      ∫ x in (T.additiveLattice n : Set F.Carrier),
          gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure -
        ((χ π : ℂ) * spectralVariable T s) ^ (n + 1) *
          ((μ.measure (T.additiveLattice n : Set F.Carrier)).toReal : ℂ) := by
  let := T.topology
  let := borel F.Carrier
  induction j, hj using Nat.le_induction with
  | base =>
    have h := setIntegral_additiveLattice_succ_gauss T π hπ χ ψ hψ μ hs 0
    simp only [Nat.cast_zero, add_zero] at h
    rw [Nat.cast_one, h, setIntegral_gaussShell_unramified T π hπ χ h0 ψ.toAddChar μ s,
      setIntegral_gaussShell_character T μ ψ hψ, ite_eq_right (by omega), ite_eq_left (by omega),
      add_sub_cancel_right]
    ring
  | succ j hj ih =>
    rw [show n + ((j + 1 : ℕ) : ℤ) = n + j + 1 by push_cast; ring,
      setIntegral_additiveLattice_succ_gauss T π hπ χ ψ hψ μ hs j, ih,
      setIntegral_gaussShell_unramified T π hπ χ h0 ψ.toAddChar μ s,
      setIntegral_gaussShell_character T μ ψ hψ, ite_eq_right (by omega), ite_eq_right (by omega)]
    ring

end Langlands.LocalFactor.PadicAbelian

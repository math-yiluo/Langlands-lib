import Langlands.LocalFactor.Abelian.GaussShellVanishing
import Langlands.LocalFactor.Harmonic.NormalizationProof
import Langlands.HarmonicAnalysis.PadicFourierClosureProof
import Langlands.HarmonicAnalysis.PadicLatticeTopology

/-!
# The dual epsilon identity

For dual Haar measures, Tate's epsilon expressions of `χ, ψ` at `s` and of
`χ⁻¹, ψ⁻¹` at `1 - s` multiply to one. In the ramified case the Gauss product is
obtained from Fourier inversion applied to the test function `χ⁻¹ · 1_{O^×}`,
whose plus Fourier transform is computed by Gauss shell vanishing.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero ComplexConjugate

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

theorem quasicharacter_inv_apply (χ : Character) (v : F.Carrierˣ) : χ⁻¹ v = (χ v)⁻¹ := rfl

theorem characterExtension_inv (χ : Character) (x : F.Carrier) :
    characterExtension T χ⁻¹ x = (characterExtension T χ x)⁻¹ := by
  unfold characterExtension
  split_ifs with hx
  · simp
  · rw [quasicharacter_inv_apply, Units.val_inv_eq_inv_val]

theorem characterExtension_one (χ : Character) : characterExtension T χ 1 = 1 := by
  unfold characterExtension
  have h : Units.mk0 (1 : F.Carrier) one_ne_zero = 1 := Units.ext rfl
  simp only [one_ne_zero, dite_false, h, map_one, Units.val_one]

theorem integralUnits_eq_gaussShell_zero : integralUnits T = gaussShell T 0 := by
  ext x
  simp [integralUnits, gaussShell]

theorem mem_integralUnits_iff_valuation (x : F.Carrier) :
    x ∈ integralUnits T ↔ T.discreteValuation x = 1 := by
  rw [integralUnits_eq_gaussShell_zero, mem_gaussShell_iff_valuation, WithZero.exp_zero]

private theorem exp_neg_nat_lt_one {a : ℕ} (ha : a ≠ 0) :
    (WithZero.exp (-(a : ℤ)) : ℤᵐ⁰) < 1 := by
  simpa using (WithZero.exp_lt_exp.mpr (show -(a : ℤ) < 0 by omega))

/-- The ramified test function `χ⁻¹ · 1_{O^×}` is invariant under the lattice of
level `-a`. -/
theorem ramifiedTest_eq_of_sub_mem (χ : Character) {a : ℕ} (hχ : ConductorAt T χ a)
    (ha : a ≠ 0) {x y : F.Carrier} (hxy : y - x ∈ T.additiveLattice (-(a : ℤ))) :
    (integralUnits T).indicator (fun z => (characterExtension T χ z)⁻¹) y =
      (integralUnits T).indicator (fun z => (characterExtension T χ z)⁻¹) x := by
  have hxy' : T.discreteValuation (y - x) ≤ WithZero.exp (-(a : ℤ)) := hxy
  have hδ : T.discreteValuation (y - x) < 1 := hxy'.trans_lt (exp_neg_nat_lt_one ha)
  have hiff : x ∈ integralUnits T ↔ y ∈ integralUnits T := by
    rw [mem_integralUnits_iff_valuation, mem_integralUnits_iff_valuation]
    constructor
    · intro hx
      have hy : y = x + (y - x) := by ring
      rw [hy, T.discreteValuation.map_add_eq_of_lt_left (by rw [hx]; exact hδ), hx]
    · intro hy1
      have hx' : x = y + -(y - x) := by ring
      rw [hx', T.discreteValuation.map_add_eq_of_lt_left
        (by rw [Valuation.map_neg, hy1]; exact hδ), hy1]
  by_cases hx : x ∈ integralUnits T
  · have hy := hiff.mp hx
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    have hx0 : x ≠ 0 := hx.1
    have hxv := (mem_integralUnits_iff_valuation T x).mp hx
    set w : F.Carrier := 1 + (y - x) / x with hw
    have hw1 : T.discreteValuation (w - 1) ≤ WithZero.exp (-(a : ℤ)) := by
      rw [show w - 1 = (y - x) / x by rw [hw]; ring, map_div₀, hxv, div_one]
      exact hxy'
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, map_one] at hw1
      exact absurd hw1 (not_le.mpr (exp_neg_nat_lt_one ha))
    have hlevel : unitLevel T a (Units.mk0 w hw0) := by
      simp only [unitLevel, ha, ite_false, Units.val_mk0]
      exact hw1
    have hχw : (χ (Units.mk0 w hw0) : ℂ) = 1 := by
      rw [hχ.1 _ hlevel, Units.val_one]
    have hyw : y = ((Units.mk0 w hw0 : F.Carrierˣ) : F.Carrier) * x := by
      rw [Units.val_mk0, hw, add_mul, one_mul, div_mul_cancel₀ _ hx0]
      ring
    rw [hyw, characterExtension_unit_mul, hχw, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hiff.mpr h))]

theorem ramifiedTest_isLocallyConstant (χ : Character) {a : ℕ} (hχ : ConductorAt T χ a)
    (ha : a ≠ 0) :
    letI := T.topology
    IsLocallyConstant
      ((integralUnits T).indicator (fun z => (characterExtension T χ z)⁻¹)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (T.additiveLattice (-(a : ℤ)) : Set F.Carrier), ?_, ?_, ?_⟩
  · exact (T.isOpen_additiveLattice _).preimage (continuous_id.sub continuous_const)
  · simp only [Set.mem_preimage, sub_self, SetLike.mem_coe]
    exact (T.additiveLattice _).zero_mem
  · intro y hy
    exact ramifiedTest_eq_of_sub_mem T χ hχ ha hy

theorem ramifiedTest_hasCompactSupport (χ : Character) :
    letI := T.topology
    HasCompactSupport
      ((integralUnits T).indicator (fun z => (characterExtension T χ z)⁻¹)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply HasCompactSupport.intro (T.isCompact_additiveLattice 0)
  intro x hx
  apply Set.indicator_of_notMem
  intro hU
  apply hx
  rw [SetLike.mem_coe, T.mem_additiveLattice, (mem_integralUnits_iff_valuation T x).mp hU,
    WithZero.exp_zero]

/-- Scaling a shell by a unit `b` multiplies Haar integrals by `|b|⁻¹`. -/
theorem setIntegral_gaussShell_mul (μ : LocalHaar) (b : F.Carrierˣ) (d e : ℤ)
    (hde : e = d + T.ord (b : F.Carrier)) (g : F.Carrier → ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x in gaussShell T e, g ((b : F.Carrier) * x) ∂μ.measure =
      ((T.normalizedAbs (b : F.Carrier))⁻¹ : ℝ) • ∫ x in gaussShell T d, g x ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hmap := HarmonicAnalysis.padicScalarHaarScaling F T μ.measure b
  have hsub := (Homeomorph.mulLeft₀ (b : F.Carrier) b.ne_zero).measurableEmbedding.setIntegral_map
    (μ := μ.measure) g (gaussShell T d)
  calc
    _ = ∫ x in (fun x => (b : F.Carrier) * x) ⁻¹' gaussShell T d,
        g ((b : F.Carrier) * x) ∂μ.measure := by rw [preimage_mul_gaussShell, hde]
    _ = ∫ y in gaussShell T d, g y ∂μ.measure.map (fun x => (b : F.Carrier) * x) := hsub.symm
    _ = ((T.normalizedAbsUnits b : NNReal)⁻¹) • ∫ y in gaussShell T d, g y ∂μ.measure := by
        rw [hmap, Measure.restrict_smul, integral_smul_nnreal_measure]
    _ = _ := by rw [NNReal.smul_def, NNReal.coe_inv, T.normalizedAbsUnits_coe]

/-- The plus Fourier integral of the ramified test function is supported on the
conductor shell, where it is `q^(-(n+a))` times the Gauss integral times `χ`. -/
theorem fourier_ramifiedTest (μ : LocalHaar) (χ : Character) {a : ℕ}
    (hχ : ConductorAt T χ a) (ha : a ≠ 0) (ψ : AddChar F.Carrier Circle) {n : ℤ}
    (hψ : AdditiveConductorAt T ψ n) (y : F.Carrier) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∫ x, (ψ (x * y) : ℂ) *
        (integralUnits T).indicator (fun z => (characterExtension T χ z)⁻¹) x ∂μ.measure =
      (gaussShell T (n + a)).indicator (fun z =>
        Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) *
          (∫ x in gaussShell T (n + a), gaussIntegrand T χ ψ 0 x ∂μ.measure) *
          characterExtension T χ z) y := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hU := integralUnits_eq_gaussShell_zero T
  have hind : (fun x => (ψ (x * y) : ℂ) *
      (integralUnits T).indicator (fun z => (characterExtension T χ z)⁻¹) x) =
      (integralUnits T).indicator
        (fun x => (ψ (x * y) : ℂ) * (characterExtension T χ x)⁻¹) := by
    funext x
    by_cases hx : x ∈ integralUnits T
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  rw [hind, integral_indicator (by rw [hU]; exact gaussShell_measurableSet T 0), hU]
  by_cases hy : y = 0
  · subst hy
    have hnot : (0 : F.Carrier) ∉ gaussShell T (n + a) := fun h => h.1 rfl
    rw [Set.indicator_of_notMem hnot]
    have h := gauss_shell_integral_eq_zero_of_lt T μ χ hχ ha (1 : AddChar F.Carrier Circle) 0
      (fun _ _ => AddChar.one_apply _) 0 (by omega)
    rw [← h]
    apply setIntegral_congr_fun (gaussShell_measurableSet T 0)
    intro x _
    simp [gaussIntegrand_zero_apply]
  · set b : F.Carrierˣ := Units.mk0 y hy with hb
    have hby : (b : F.Carrier) = y := Units.val_mk0 hy
    have hcongr : ∫ x in gaussShell T 0, (ψ (x * y) : ℂ) * (characterExtension T χ x)⁻¹
          ∂μ.measure =
        ∫ x in gaussShell T 0, (χ b : ℂ) * gaussIntegrand T χ ψ 0 ((b : F.Carrier) * x)
          ∂μ.measure := by
      apply setIntegral_congr_fun (gaussShell_measurableSet T 0)
      intro x _
      simp only
      rw [gaussIntegrand_zero_apply, characterExtension_unit_mul, hby, mul_comm x y, mul_inv,
        ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (χ b).ne_zero, one_mul, mul_comm]
    rw [hcongr, setIntegral_gaussShell_mul T μ b (-T.ord (b : F.Carrier)) 0 (by ring)
      (fun z => (χ b : ℂ) * gaussIntegrand T χ ψ 0 z), integral_const_mul]
    by_cases hd : -T.ord (b : F.Carrier) = n + a
    · have hmem : y ∈ gaussShell T (n + a) := ⟨hy, by rw [← hby]; omega⟩
      rw [Set.indicator_of_mem hmem, hd]
      have hcE : characterExtension T χ y = (χ b : ℂ) := by
        simp only [characterExtension, hy, dite_false, hb]
      have habs : ((T.normalizedAbs (b : F.Carrier))⁻¹ : ℝ) =
          Real.exp (-((n + (a : ℤ) : ℤ) : ℝ) * Real.log (T.residueCardinality : ℝ)) := by
        rw [← Real.exp_log (T.normalizedAbs_pos b.ne_zero), ← Real.exp_neg,
          log_normalizedAbs_unit, ← hd]
        congr 1
        push_cast
        ring
      rw [hcE, Complex.real_smul, habs, Complex.ofReal_exp]
      push_cast
      ring_nf
    · have hnot : y ∉ gaussShell T (n + a) := by
        intro h
        apply hd
        have h2 := h.2
        rw [← hby] at h2
        omega
      rw [Set.indicator_of_notMem hnot,
        gauss_shell_integral_eq_zero T μ χ hχ ha ψ hψ _ hd 0, mul_zero, smul_zero]

/-- Tate's Gauss product for dual Haar measures: with `μ(O) ν(O) = q^(-n)`, the
ramified Gauss integrals of `(χ, ψ)` and `(χ⁻¹, ψ⁻¹)` multiply to `q^(n+a)`. -/
theorem gauss_mul_gauss_inv (μ : LocalHaar) (χ : Character) {a : ℕ}
    (hχ : ConductorAt T χ a) (ha : a ≠ 0) (ψ : AdditiveCharacter) (n : ℤ)
    (ν : BorelMeasure T) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    AdditiveConductorAt T ψ.toAddChar n →
    ν.IsAddHaarMeasure →
    (μ.measure (integerRing T)).toReal * (ν (integerRing T)).toReal =
      (T.residueCardinality : ℝ) ^ (-n) →
    Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) *
      (∫ x in gaussShell T (n + a), gaussIntegrand T χ ψ.toAddChar 0 x ∂μ.measure) *
      (∫ x in gaussShell T (n + a), gaussIntegrand T χ⁻¹ ψ.toAddChar⁻¹ 0 x ∂ν) = 1 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro hψ hν hmass
  set f := (integralUnits T).indicator (fun z => (characterExtension T χ z)⁻¹) with hf
  set C := Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ))
  set G := ∫ x in gaussShell T (n + a), gaussIntegrand T χ ψ.toAddChar 0 x ∂μ.measure
  set S := gaussShell T (n + a)
  have hlc : IsLocallyConstant f := ramifiedTest_isLocallyConstant T χ hχ ha
  have hcs : HasCompactSupport f := ramifiedTest_hasCompactSupport T χ
  have hn : n = T.additiveConductor ψ := (additiveConductorAt_iff T ψ n).mp hψ
  have hgreat := T.isGreatest_fractionalIdeal_triviality ψ
  rw [← hn] at hgreat
  have hnorm := LocalFactors.padicFourierNormalization p F T ψ.toAddChar ψ.continuous_toFun
    ψ.nontrivial n hgreat
  have hdual := (hnorm.1 μ.measure ν inferInstance hν).mpr hmass
  have hinv := hdual f hlc hcs (-1)
  have hcl1 := HarmonicAnalysis.padicFourierClosure p F T ψ.toAddChar ψ.continuous_toFun
    ψ.nontrivial μ.measure inferInstance f hlc hcs
  have hFf : Fourier.fourierIntegral ψ.toAddChar⁻¹ μ.measure f =
      S.indicator (fun z => C * G * characterExtension T χ z) := by
    funext y
    rw [hcl1.2.2.1 y]
    exact fourier_ramifiedTest T μ χ hχ ha ψ.toAddChar hψ y
  have hlc2 := hcl1.2.2.2.1
  have hcs2 := hcl1.2.2.2.2.1
  rw [hFf] at hlc2 hcs2 hinv
  have hcl2 := HarmonicAnalysis.padicFourierClosure p F T ψ.toAddChar ψ.continuous_toFun
    ψ.nontrivial ν hν _ hlc2 hcs2
  rw [hcl2.2.2.1 (-1), neg_neg, hf, Set.indicator_of_mem (show (1 : F.Carrier) ∈ integralUnits T
    from ⟨one_ne_zero, T.ord_one⟩), characterExtension_one, inv_one] at hinv
  have hind : (fun x => (ψ.toAddChar (x * -1) : ℂ) *
      S.indicator (fun z => C * G * characterExtension T χ z) x) =
      S.indicator (fun x => C * G * gaussIntegrand T χ⁻¹ ψ.toAddChar⁻¹ 0 x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, gaussIntegrand_zero_apply,
        characterExtension_inv, inv_inv, AddChar.inv_apply, mul_neg_one]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  rw [hind, integral_indicator (gaussShell_measurableSet T _), integral_const_mul] at hinv
  exact hinv


private theorem exp_int_mul_log_residue (n : ℤ) :
    Complex.exp ((n : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) =
      (((T.residueCardinality : ℝ) ^ n : ℝ) : ℂ) := by
  rw [Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log (residueCardinality_pos' T)]
  push_cast
  rfl

/-- Tate's dual epsilon identity at explicit conductor levels: for Haar measures
with `μ(O) ν(O) = q^(-n)`, `ε(χ, ψ, μ, s) ε(χ⁻¹, ψ⁻¹, ν, 1 - s) = 1`. -/
theorem epsilonAt_mul_epsilonAt_inv (π : F.Carrierˣ) (χ : Character) {a : ℕ}
    (hχ : ConductorAt T χ a) (ψ : AdditiveCharacter) (n : ℤ) (μ : LocalHaar)
    (ν : BorelMeasure T) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    AdditiveConductorAt T ψ.toAddChar n →
    ν.IsAddHaarMeasure →
    (μ.measure (integerRing T)).toReal * (ν (integerRing T)).toReal =
      (T.residueCardinality : ℝ) ^ (-n) →
    ∀ s : ℂ, epsilonAt T π χ ψ.toAddChar μ.measure a n s *
      epsilonAt T π χ⁻¹ ψ.toAddChar⁻¹ ν a n (1 - s) = 1 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  intro hψ hν hmass s
  have hq := residueCardinality_pos' T
  have hqm : (((T.residueCardinality : ℝ) ^ n : ℝ) : ℂ) *
      (((μ.measure (integerRing T)).toReal : ℂ) * ((ν (integerRing T)).toReal : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, hmass, ← Complex.ofReal_mul, ← zpow_add₀ hq.ne', add_neg_cancel,
      zpow_zero, Complex.ofReal_one]
  by_cases ha : a = 0
  · unfold epsilonAt
    simp only [ha, ↓reduceIte]
    rw [quasicharacter_inv_apply, Units.val_inv_eq_inv_val, inv_zpow, sub_sub_cancel]
    have he : Complex.exp ((n : ℂ) * (1 - s) * (Real.log (T.residueCardinality : ℝ) : ℂ)) *
        Complex.exp ((n : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)) =
        Complex.exp ((n : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      ring_nf
    calc _ = ((χ π : ℂ) ^ n * ((χ π : ℂ) ^ n)⁻¹) *
          (Complex.exp ((n : ℂ) * (1 - s) * (Real.log (T.residueCardinality : ℝ) : ℂ)) *
            Complex.exp ((n : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ))) *
          (((μ.measure (integerRing T)).toReal : ℂ) * ((ν (integerRing T)).toReal : ℂ)) := by
          ring
      _ = 1 := by
          rw [mul_inv_cancel₀ (zpow_ne_zero _ (χ π).ne_zero), he, exp_int_mul_log_residue,
            one_mul, hqm]
  · rw [epsilonAt_eq_zero_mul T π χ ψ.toAddChar μ.measure a n s,
      epsilonAt_eq_zero_mul T π χ⁻¹ ψ.toAddChar⁻¹ ν a n (1 - s)]
    unfold epsilonAt
    simp only [ha, ↓reduceIte]
    have hG := gauss_mul_gauss_inv T μ χ hχ ha ψ n ν hψ hν hmass
    have he : Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * s *
          (Real.log (T.residueCardinality : ℝ) : ℂ)) *
        Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * (1 - s) *
          (Real.log (T.residueCardinality : ℝ) : ℂ)) =
        Complex.exp (-((n + (a : ℤ) : ℤ) : ℂ) * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      ring_nf
    linear_combination
      ((∫ x in gaussShell T (n + a), gaussIntegrand T χ ψ.toAddChar 0 x ∂μ.measure) *
        (∫ x in gaussShell T (n + a), gaussIntegrand T χ⁻¹ ψ.toAddChar⁻¹ 0 x ∂ν)) * he + hG

/-- For every Haar measure there is a Haar measure dual to it for `ψ`. -/
theorem exists_dual_measure (ψ : AdditiveCharacter) (n : ℤ) (μ : BorelMeasure T) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    AdditiveConductorAt T ψ.toAddChar n → μ.IsAddHaarMeasure →
    ∃ ν : BorelMeasure T, ν.IsAddHaarMeasure ∧
      (μ (integerRing T)).toReal * (ν (integerRing T)).toReal =
        (T.residueCardinality : ℝ) ^ (-n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro hψ hμ
  have hn : n = T.additiveConductor ψ := (additiveConductorAt_iff T ψ n).mp hψ
  have hgreat := T.isGreatest_fractionalIdeal_triviality ψ
  rw [← hn] at hgreat
  have hnorm := LocalFactors.padicFourierNormalization p F T ψ.toAddChar ψ.continuous_toFun
    ψ.nontrivial n hgreat
  obtain ⟨htd, hdu⟩ := LocalFactors.padicFourierDuality p F T
  obtain ⟨ν, ⟨hν, hdual⟩, -⟩ := (hdu ψ.toAddChar ψ.continuous_toFun ψ.nontrivial).1 μ hμ
  exact ⟨ν, hν, (hnorm.1 μ ν hμ hν).mp hdual⟩

/-- The epsilon expression never vanishes. -/
theorem epsilonAt_ne_zero (π : F.Carrierˣ) (χ : Character) {a : ℕ} (hχ : ConductorAt T χ a)
    (ψ : AdditiveCharacter) (n : ℤ) (μ : LocalHaar) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    AdditiveConductorAt T ψ.toAddChar n →
    ∀ s : ℂ, epsilonAt T π χ ψ.toAddChar μ.measure a n s ≠ 0 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  intro hψ s h0
  obtain ⟨ν, hν, hmass⟩ := exists_dual_measure T ψ n μ.measure hψ inferInstance
  have h := epsilonAt_mul_epsilonAt_inv T π χ hχ ψ n μ ν hψ hν hmass s
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- For a unitary quasicharacter, conjugating the Gauss integrand inverts both
characters and conjugates the spectral variable. -/
theorem conj_gaussIntegrand (χ : Character) (hχu : ∀ v : F.Carrierˣ, ‖(χ v : ℂ)‖ = 1)
    (ψ : AddChar F.Carrier Circle) (s : ℂ) (x : F.Carrier) :
    conj (gaussIntegrand T χ ψ s x) = gaussIntegrand T χ⁻¹ ψ⁻¹ (conj s) x := by
  unfold gaussIntegrand
  rw [characterExtension_inv, AddChar.inv_apply', Circle.coe_inv_eq_conj]
  by_cases hx : x = 0
  · simp [characterExtension, hx]
  · have hu : ‖characterExtension T χ x‖ = 1 := by
      simp only [characterExtension, hx, dite_false]
      exact hχu _
    rw [map_mul, map_mul, map_inv₀, ← Complex.inv_eq_conj hu, ← Complex.exp_conj, map_mul,
      map_neg, Complex.conj_ofReal]

/-- For a unitary quasicharacter, conjugating the epsilon expression inverts both
characters and conjugates the spectral variable. -/
theorem conj_epsilonAt (π : F.Carrierˣ) (χ : Character)
    (hχu : ∀ v : F.Carrierˣ, ‖(χ v : ℂ)‖ = 1) (ψ : AddChar F.Carrier Circle)
    (μ : BorelMeasure T) (a : ℕ) (n : ℤ) (s : ℂ) :
    conj (epsilonAt T π χ ψ μ a n s) = epsilonAt T π χ⁻¹ ψ⁻¹ μ a n (conj s) := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  unfold epsilonAt
  split_ifs with ha
  · rw [quasicharacter_inv_apply, Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hχu π)]
    simp only [map_mul, map_sub, map_one, map_intCast, map_zpow₀, Complex.conj_ofReal,
      ← Complex.exp_conj]
  · rw [← integral_conj]
    congr 1
    funext x
    exact conj_gaussIntegrand T χ hχu ψ s x

/-- For a unitary quasicharacter and a self-dual Haar measure, the central
epsilon value has absolute value one. -/
theorem norm_epsilonAt_half (π : F.Carrierˣ) (χ : Character) {a : ℕ} (hχ : ConductorAt T χ a)
    (ψ : AdditiveCharacter) (n : ℤ) (μ : LocalHaar) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    AdditiveConductorAt T ψ.toAddChar n →
    (∀ v : F.Carrierˣ, ‖(χ v : ℂ)‖ = 1) →
    (μ.measure (integerRing T)).toReal = (T.residueCardinality : ℝ) ^ (-(n : ℝ) / 2) →
    ‖epsilonAt T π χ ψ.toAddChar μ.measure a n (1 / 2)‖ = 1 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  intro hψ hχu hμ
  have hq := residueCardinality_pos' T
  have hmass : (μ.measure (integerRing T)).toReal * (μ.measure (integerRing T)).toReal =
      (T.residueCardinality : ℝ) ^ (-n) := by
    rw [hμ, ← Real.rpow_add hq, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have h := epsilonAt_mul_epsilonAt_inv T π χ hχ ψ n μ μ.measure hψ inferInstance hmass (1 / 2)
  have hc : (1 : ℂ) - 1 / 2 = conj (1 / 2 : ℂ) := by
    rw [map_div₀, map_one, map_ofNat]
    norm_num
  rw [hc, ← conj_epsilonAt T π χ hχu ψ.toAddChar μ.measure a n, Complex.mul_conj'] at h
  have h2 : ‖epsilonAt T π χ ψ.toAddChar μ.measure a n (1 / 2)‖ ^ 2 = 1 := by
    exact_mod_cast h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

end Langlands.LocalFactor.PadicAbelian

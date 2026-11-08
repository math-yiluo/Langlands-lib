import Langlands.LocalFactor.Abelian.EulerTestFourier

noncomputable section

open MeasureTheory Filter Topology
open scoped WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

/-- The Mellin coefficient at the actual chosen uniformizer's kth power. -/
def shellMellinTerm (f : F.Carrier → ℂ) (χ : Character) (s : ℂ) (k : ℤ) : ℂ :=
  f ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) *
    ((χ (uniformizerUnit T) : ℂ) * spectralVariable T s) ^ k

theorem shellMellinTerm_eq_exp (f : F.Carrier → ℂ) (χ : Character) (s : ℂ) (k : ℤ) :
    shellMellinTerm T f χ s k =
      f ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) *
        (χ (uniformizerUnit T) : ℂ) ^ k *
          Complex.exp (-(k : ℂ) * s * (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
  rw [shellMellinTerm, mul_zpow, spectralVariable_zpow]
  ring

/-- A geometric series supported on the nonnegative integers. -/
theorem hasSum_int_geometric_nonneg (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℤ => if 0 ≤ k then z ^ k else 0) (1 - z)⁻¹ := by
  have hpos : HasSum (fun k : ℕ => if 0 ≤ (k : ℤ) then z ^ (k : ℤ) else 0)
      (1 - z)⁻¹ := by
    simpa only [Int.natCast_nonneg, ite_true, zpow_natCast] using
      hasSum_geometric_of_norm_lt_one hz
  have hneg : HasSum (fun k : ℕ => if 0 ≤ -((k : ℤ) + 1) then
      z ^ (-((k : ℤ) + 1)) else 0) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
    funext k
    rw [ite_eq_right (by omega)]
  simpa only [add_zero] using
    (HasSum.of_nat_of_neg_add_one (f := fun k : ℤ => if 0 ≤ k then z ^ k else 0) hpos hneg)

/-- A translated geometric tail, including any finite negative part. -/
theorem hasSum_int_geometric_ge (z : ℂ) (hz : ‖z‖ < 1) (hne : z ≠ 0) (m : ℤ) :
    HasSum (fun k : ℤ => if m ≤ k then z ^ k else 0) (z ^ m * (1 - z)⁻¹) := by
  apply ((Equiv.addRight m).hasSum_iff).mp
  convert (hasSum_int_geometric_nonneg z hz).mul_left (z ^ m) using 1
  funext k
  change (if m ≤ k + m then z ^ (k + m) else 0) =
    z ^ m * (if 0 ≤ k then z ^ k else 0)
  by_cases hk : 0 ≤ k
  · rw [ite_eq_left (by omega), ite_eq_left hk, zpow_add₀ hne]
    ring
  · rw [ite_eq_right (by omega), ite_eq_right hk, mul_zero]

theorem uniformizer_pow_mem_additiveLattice (n k : ℤ) :
    ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) ∈ T.additiveLattice n ↔ -n ≤ k := by
  rw [T.mem_additiveLattice, uniformizerUnit_zpow_value, WithZero.exp_le_exp]
  omega

theorem uniformizer_pow_mem_integralUnits (k : ℤ) :
    ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) ∈ integralUnits T ↔ k = 0 := by
  change (((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) ≠ 0 ∧
    T.ord ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) = 0) ↔ k = 0
  rw [and_iff_right (uniformizerUnit T ^ k).ne_zero, Units.val_zpow_eq_zpow_val,
    T.ord_zpow, uniformizerUnit_ord, mul_one]

theorem multiplicativeConductor_inv_eq (χ : Character) :
    T.multiplicativeConductor χ⁻¹ = T.multiplicativeConductor χ := by
  exact ((conductorAt_iff T χ⁻¹ _).mp
    (conductorAt_inv T χ _ ((conductorAt_iff T χ _).mpr rfl))).symm

theorem eulerTest_uniformizer_pow_unramified (χ : Character)
    (hχ : T.multiplicativeConductor χ = 0) (k : ℤ) :
    eulerTest T χ ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) =
      if 0 ≤ k then 1 else 0 := by
  classical
  rw [show eulerTest T χ _ = (eulerTest T χ : F.Carrier → ℂ) _ from rfl,
    eulerTest_coe, ite_eq_left hχ, integerRing_eq_lattice_zero]
  simp only [Set.indicator_apply, SetLike.mem_coe,
    uniformizer_pow_mem_additiveLattice, neg_zero]

theorem eulerTest_uniformizer_pow_ramified (χ : Character)
    (hχ : T.multiplicativeConductor χ ≠ 0) (k : ℤ) :
    eulerTest T χ ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) =
      if k = 0 then 1 else 0 := by
  classical
  rw [show eulerTest T χ _ = (eulerTest T χ : F.Carrier → ℂ) _ from rfl,
    eulerTest_coe, ite_eq_right hχ]
  by_cases hk : k = 0
  · subst k
    rw [zpow_zero, Units.val_one, Set.indicator_of_mem
      (show (1 : F.Carrier) ∈ integralUnits T from ⟨one_ne_zero, T.ord_one⟩),
      characterExtension_one, inv_one, ite_eq_left rfl]
  · rw [Set.indicator_of_notMem (by simpa only [uniformizer_pow_mem_integralUnits] using hk),
      ite_eq_right hk]

/-- The original test has exactly the local Euler series. -/
theorem hasSum_eulerTest (χ : Character) (s : ℂ)
    (hs : ConvergesAt T (uniformizerUnit T) χ s) :
    HasSum (shellMellinTerm T (eulerTest T χ) χ s) (lFactor T χ s) := by
  classical
  by_cases hχ : T.multiplicativeConductor χ = 0
  · have h := hasSum_int_geometric_nonneg
      ((χ (uniformizerUnit T) : ℂ) * spectralVariable T s)
      ((convergesAt_iff_norm_lt_one T _ χ s).mp hs)
    convert h using 1
    · funext k
      rw [shellMellinTerm, eulerTest_uniformizer_pow_unramified T χ hχ]
      split_ifs <;> simp
    · simp only [lFactor, lFactorAt, ite_eq_left hχ]
  · convert hasSum_ite_eq (0 : ℤ) (1 : ℂ) using 1
    · funext k
      rw [shellMellinTerm, eulerTest_uniformizer_pow_ramified T χ hχ]
      by_cases hk : k = 0 <;> simp [hk]
    · simp only [lFactor, lFactorAt, ite_eq_right hχ]

/-- The Fourier-transformed unramified test gives a translated geometric tail. -/
theorem hasSum_fourier_eulerTest_unramified (χ : Character)
    (hχ : T.multiplicativeConductor χ = 0) (ψ : AdditiveCharacter) (μ : LocalHaar)
    (s : ℂ) (hs : ConvergesAt T (uniformizerUnit T) χ⁻¹ s) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HasSum (shellMellinTerm T
      (HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ)) χ⁻¹ s)
      (epsilon T χ ψ μ.measure (1 - s) * lFactor T χ⁻¹ s) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let z : ℂ := (χ⁻¹ (uniformizerUnit T) : ℂ) * spectralVariable T s
  have hz : ‖z‖ < 1 := (convergesAt_iff_norm_lt_one T _ χ⁻¹ s).mp hs
  have hne : z ≠ 0 := mul_ne_zero (χ⁻¹ (uniformizerUnit T)).ne_zero
    (spectralVariable_ne_zero T s)
  have h := (hasSum_int_geometric_ge z hz hne (-T.additiveConductor ψ)).mul_left
    ((μ.measure (integerRing T)).toReal : ℂ)
  have hn : T.multiplicativeConductor χ⁻¹ = 0 := by
    rw [multiplicativeConductor_inv_eq, hχ]
  have he : ((μ.measure (integerRing T)).toReal : ℂ) * z ^ (-T.additiveConductor ψ) =
      epsilon T χ ψ μ.measure (1 - s) := by
    rw [epsilon, epsilonAt, ite_eq_left hχ]
    dsimp only [z]
    rw [mul_zpow, quasicharacter_inv_apply, Units.val_inv_eq_inv_val,
      inv_zpow, zpow_neg, inv_inv, spectralVariable_zpow]
    simp only [Int.cast_neg, neg_neg, sub_sub_cancel]
    ring
  convert h using 1
  · funext k
    rw [shellMellinTerm, fourier_eulerTest_unramified T χ hχ ψ μ]
    simp only [Set.indicator_apply, SetLike.mem_coe, uniformizer_pow_mem_additiveLattice]
    split_ifs <;> simp [z]
  · rw [← mul_assoc, he]
    simp only [lFactor, lFactorAt, ite_eq_left hn]
    rfl

/-- The transformed ramified test has only one nonzero Mellin coefficient. -/
theorem shellMellinTerm_fourier_eulerTest_ramified (χ : Character)
    (hχ : T.multiplicativeConductor χ ≠ 0) (ψ : AdditiveCharacter) (μ : LocalHaar)
    (s : ℂ) (k : ℤ) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    shellMellinTerm T (HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ)) χ⁻¹ s k =
      if k = -(T.additiveConductor ψ + (T.multiplicativeConductor χ : ℤ)) then
        epsilon T χ ψ μ.measure (1 - s) else 0 := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  dsimp only [shellMellinTerm]
  rw [fourier_eulerTest_ramified T χ hχ ψ μ]
  have hmem : ((uniformizerUnit T ^ k : F.Carrierˣ) : F.Carrier) ∈
      gaussShell T (T.additiveConductor ψ + T.multiplicativeConductor χ) ↔
      k = -(T.additiveConductor ψ + (T.multiplicativeConductor χ : ℤ)) := by
    change (_ ≠ 0 ∧ _ = _) ↔ _
    rw [and_iff_right (uniformizerUnit T ^ k).ne_zero, Units.val_zpow_eq_zpow_val,
      T.ord_zpow, uniformizerUnit_ord, mul_one]
  by_cases hk : k = -(T.additiveConductor ψ + (T.multiplicativeConductor χ : ℤ))
  · rw [Set.indicator_of_mem (hmem.mpr hk), ite_eq_left hk,
      characterExtension_unit, map_zpow, Units.val_zpow_eq_zpow_val,
      mul_zpow, quasicharacter_inv_apply, Units.val_inv_eq_inv_val, inv_zpow]
    rw [show Complex.exp (-((T.additiveConductor ψ +
        (T.multiplicativeConductor χ : ℤ) : ℤ) : ℂ) *
          (Real.log (T.residueCardinality : ℝ) : ℂ)) *
          epsilon T χ ψ μ.measure 0 * (χ (uniformizerUnit T) : ℂ) ^ k *
            (((χ (uniformizerUnit T) : ℂ) ^ k)⁻¹ * spectralVariable T s ^ k) =
        epsilon T χ ψ μ.measure 0 *
          (Complex.exp (-((T.additiveConductor ψ +
            (T.multiplicativeConductor χ : ℤ) : ℤ) : ℂ) *
              (Real.log (T.residueCardinality : ℝ) : ℂ)) * spectralVariable T s ^ k) by
      field_simp]
    rw [spectralVariable_zpow, ← Complex.exp_add]
    simp only [epsilon]
    rw [epsilonAt_eq_zero_mul T (uniformizerUnit T) χ ψ.toAddChar μ.measure
      (T.multiplicativeConductor χ) (T.additiveConductor ψ) (1 - s)]
    congr 2
    rw [hk, Int.cast_neg]
    ring
  · rw [Set.indicator_of_notMem (fun h => hk (hmem.mp h)), ite_eq_right hk, zero_mul]

/-- The Fourier-transformed test has epsilon times the dual Euler series. -/
theorem hasSum_fourier_eulerTest (χ : Character) (ψ : AdditiveCharacter) (μ : LocalHaar)
    (s : ℂ) (hs : ConvergesAt T (uniformizerUnit T) χ⁻¹ s) :
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    let := borel F.Carrier
    let : BorelSpace F.Carrier := ⟨rfl⟩
    HasSum (shellMellinTerm T
      (HarmonicAnalysis.fourierTransform ψ μ (eulerTest T χ)) χ⁻¹ s)
      (epsilon T χ ψ μ.measure (1 - s) * lFactor T χ⁻¹ s) := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  by_cases hχ : T.multiplicativeConductor χ = 0
  · exact hasSum_fourier_eulerTest_unramified T χ hχ ψ μ s hs
  · have hn : T.multiplicativeConductor χ⁻¹ ≠ 0 := by
      rw [multiplicativeConductor_inv_eq]; exact hχ
    convert hasSum_ite_eq
      (-(T.additiveConductor ψ + (T.multiplicativeConductor χ : ℤ)))
      (epsilon T χ ψ μ.measure (1 - s)) using 1
    · funext k
      exact shellMellinTerm_fourier_eulerTest_ramified T χ hχ ψ μ s k
    · simp only [lFactor, lFactorAt, ite_eq_right hn, mul_one]

end Langlands.LocalFactor.PadicAbelian
